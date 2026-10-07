#!/usr/bin/env julia
# ============================================================================
#
#
# Author: Ian Carter Kulani, MSc
# HERMIT-CRAB-v1
# A Network Security Tool for IP Management, Blockchain-Based IP Storage,
# Traffic Monitoring, and Attack Detection (DoS/DDoS/HTTP/HTTPS Floods)
# Language: Julia  (ZERO external dependencies)
# ============================================================================

module HermitCrabV1

using Sockets
using Dates
using Random
using Printf
using SHA
using Statistics

# ============================================================================
# SECTION 1: CONSTANTS AND CONFIGURATION
# ============================================================================

const APP_NAME = "hermit-crab-v1"
const APP_VERSION = "1.0.0"
const GENESIS_HASH = "0"^64
const DIFFICULTY = 3  # Number of leading zeros for PoW (low for usability)

# Attack detection thresholds
const DOS_THRESHOLD = 100           # packets/sec from single IP
const DDOS_THRESHOLD = 1000         # total packets/sec across many IPs
const HTTP_FLOOD_THRESHOLD = 50     # HTTP requests/sec from single IP
const HTTPS_FLOOD_THRESHOLD = 50    # HTTPS requests/sec from single IP
const DDOS_UNIQUE_IP_THRESHOLD = 20 # unique source IPs in window
const MONITOR_WINDOW = 10           # seconds

# ============================================================================
# SECTION 2: LOGGER
# ============================================================================

mutable struct Logger
    level::Symbol  # :debug, :info, :warn, :error
    logfile::Union{Nothing, IO}
    lock::ReentrantLock
end

function Logger(level::Symbol=:info, logpath::Union{Nothing,String}=nothing)
    io = logpath === nothing ? nothing : open(logpath, "a")
    Logger(level, io, ReentrantLock())
end

function logmsg(logger::Logger, level::Symbol, msg::String)
    levels = Dict(:debug=>1, :info=>2, :warn=>3, :error=>4)
    if levels[level] >= levels[logger.level]
        lock(logger.lock)
        try
            ts = Dates.format(now(), "yyyy-mm-dd HH:MM:SS")
            line = "[$ts][$(uppercase(string(level)))] $msg"
            println(line)
            if logger.logfile !== nothing
                println(logger.logfile, line)
                flush(logger.logfile)
            end
        finally
            unlock(logger.lock)
        end
    end
end

macro loginfo(logger, msg)
    quote
        logmsg($(esc(logger)), :info, $(esc(msg)))
    end
end

macro logwarn(logger, msg)
    quote
        logmsg($(esc(logger)), :warn, $(esc(msg)))
    end
end

macro logerror(logger, msg)
    quote
        logmsg($(esc(logger)), :error, $(esc(msg)))
    end
end

macro logdebug(logger, msg)
    quote
        logmsg($(esc(logger)), :debug, $(esc(msg)))
    end
end

# ============================================================================
# SECTION 3: IP UTILITIES
# ============================================================================

struct IPRecord
    ip::String
    added_at::DateTime
    added_by::String
    note::String
end

function is_valid_ip(ip::String)::Bool
    try
        Sockets.IPv4(ip)
        return true
    catch
    end
    try
        Sockets.IPv6(ip)
        return true
    catch
    end
    return false
end

function normalize_ip(ip::String)::String
    return lowercase(strip(ip))
end

function parse_ip_list(input::String)::Vector{String}
    parts = split(replace(input, "\n" => ","), ",")
    ips = String[]
    for p in parts
        t = strip(p)
        if isempty(t)
            continue
        end
        if is_valid_ip(t)
            push!(ips, normalize_ip(t))
        end
    end
    return ips
end

# ============================================================================
# SECTION 4: BLOCKCHAIN FOR IP STORAGE
# ============================================================================

struct IPBlock
    index::Int
    timestamp::DateTime
    previous_hash::String
    data::Vector{IPRecord}
    nonce::Int
    hash::String
end

function compute_hash(index::Int, timestamp::DateTime, previous_hash::String,
                      data::Vector{IPRecord}, nonce::Int)::String
    payload = IOBuffer()
    print(payload, index)
    print(payload, string(timestamp))
    print(payload, previous_hash)
    for r in data
        print(payload, r.ip, "|", string(r.added_at), "|", r.added_by, "|", r.note, ";")
    end
    print(payload, nonce)
    return bytes2hex(sha256(take!(payload)))
end

function mine_block(index::Int, previous_hash::String,
                    data::Vector{IPRecord})::IPBlock
    ts = now()
    nonce = 0
    target = "0"^DIFFICULTY
    while true
        h = compute_hash(index, ts, previous_hash, data, nonce)
        if startswith(h, target)
            return IPBlock(index, ts, previous_hash, data, nonce, h)
        end
        nonce += 1
    end
end

mutable struct IPBlockchain
    chain::Vector{IPBlock}
    ip_index::Dict{String, Int}
    lock::ReentrantLock
end

function IPBlockchain()
    genesis = mine_block(0, GENESIS_HASH, IPRecord[])
    chain = IPBlockchain([genesis], Dict{String,Int}(), ReentrantLock())
    return chain
end

function is_chain_valid(bc::IPBlockchain)::Bool
    for i in 2:length(bc.chain)
        cur = bc.chain[i]
        prev = bc.chain[i-1]
        if cur.previous_hash != prev.hash
            return false
        end
        expected = compute_hash(cur.index, cur.timestamp, cur.previous_hash,
                                cur.data, cur.nonce)
        if expected != cur.hash
            return false
        end
    end
    return true
end

function add_ips!(bc::IPBlockchain, ips::Vector{String}, added_by::String,
                  note::String, logger::Logger)::Int
    lock(bc.lock)
    try
        new_records = IPRecord[]
        for ip in ips
            n = normalize_ip(ip)
            if !is_valid_ip(n)
                @logwarn logger "Invalid IP skipped: $ip"
                continue
            end
            if haskey(bc.ip_index, n)
                @logdebug logger "IP already exists in chain: $n"
                continue
            end
            push!(new_records, IPRecord(n, now(), added_by, note))
        end
        if isempty(new_records)
            return 0
        end
        prev = bc.chain[end]
        blk = mine_block(prev.index + 1, prev.hash, new_records)
        push!(bc.chain, blk)
        for r in new_records
            bc.ip_index[r.ip] = blk.index
        end
        @loginfo logger "Mined block #$(blk.index) with $(length(new_records)) IP(s); hash=$(blk.hash[1:16])..."
        return length(new_records)
    finally
        unlock(bc.lock)
    end
end

function ip_exists(bc::IPBlockchain, ip::String)::Bool
    lock(bc.lock)
    try
        return haskey(bc.ip_index, normalize_ip(ip))
    finally
        unlock(bc.lock)
    end
end

function list_ips(bc::IPBlockchain)::Vector{IPRecord}
    lock(bc.lock)
    try
        out = IPRecord[]
        for blk in bc.chain
            append!(out, blk.data)
        end
        return out
    finally
        unlock(bc.lock)
    end
end

function chain_stats(bc::IPBlockchain)
    lock(bc.lock)
    try
        total_ips = length(bc.ip_index)
        return Dict(
            "blocks" => length(bc.chain),
            "unique_ips" => total_ips,
            "valid" => is_chain_valid(bc),
            "last_hash" => bc.chain[end].hash
        )
    finally
        unlock(bc.lock)
    end
end

# ============================================================================
# SECTION 5: TRAFFIC MONITORING ENGINE  (no external deps)
# ============================================================================

struct PacketEvent
    timestamp::DateTime
    src_ip::String
    dst_ip::String
    src_port::Int
    dst_port::Int
    protocol::Symbol   # :tcp, :udp, :icmp, :http, :https
    size::Int
    flags::String
end

# Simple sliding window using a Vector as a FIFO
mutable struct SlidingWindow
    events::Vector{PacketEvent}
    window_sec::Int
end

SlidingWindow(window_sec::Int=MONITOR_WINDOW) = SlidingWindow(PacketEvent[], window_sec)

function push_event!(sw::SlidingWindow, ev::PacketEvent)
    push!(sw.events, ev)
    cutoff = now() - Dates.Second(sw.window_sec)
    # drop old events from the front
    i = 1
    while i <= length(sw.events) && sw.events[i].timestamp < cutoff
        i += 1
    end
    if i > 1
        deleteat!(sw.events, 1:i-1)
    end
end

# ============================================================================
# SECTION 6: ATTACK DETECTORS
# ============================================================================

abstract type AbstractDetector end

mutable struct DetectionAlert
    timestamp::DateTime
    alert_type::String
    severity::Symbol
    src_ip::String
    detail::String
end

mutable struct DoSDetector <: AbstractDetector
    per_ip_counts::Dict{String, Int}
    threshold::Int
    alerts::Vector{DetectionAlert}
end

DoSDetector(threshold::Int=DOS_THRESHOLD) = DoSDetector(Dict{String,Int}(), threshold, DetectionAlert[])

mutable struct DDoSDetector <: AbstractDetector
    total_count::Int
    unique_ips::Set{String}
    threshold_packets::Int
    threshold_ips::Int
    alerts::Vector{DetectionAlert}
end

DDoSDetector() = DDoSDetector(0, Set{String}(), DDOS_THRESHOLD,
                              DDOS_UNIQUE_IP_THRESHOLD, DetectionAlert[])

mutable struct HTTPFloodDetector <: AbstractDetector
    per_ip_counts::Dict{String, Int}
    threshold::Int
    is_https::Bool
    alerts::Vector{DetectionAlert}
end

HTTPFloodDetector(is_https::Bool, threshold::Int) =
    HTTPFloodDetector(Dict{String,Int}(), threshold, is_https, DetectionAlert[])

mutable struct DetectionEngine
    dos::DoSDetector
    ddos::DDoSDetector
    http::HTTPFloodDetector
    https::HTTPFloodDetector
    window::SlidingWindow
    all_alerts::Vector{DetectionAlert}
    lock::ReentrantLock
end

function DetectionEngine()
    DetectionEngine(
        DoSDetector(),
        DDoSDetector(),
        HTTPFloodDetector(false, HTTP_FLOOD_THRESHOLD),
        HTTPFloodDetector(true, HTTPS_FLOOD_THRESHOLD),
        SlidingWindow(),
        DetectionAlert[],
        ReentrantLock()
    )
end

function reset_counters!(de::DetectionEngine)
    lock(de.lock)
    try
        empty!(de.dos.per_ip_counts)
        empty!(de.ddos.unique_ips)
        de.ddos.total_count = 0
        empty!(de.http.per_ip_counts)
        empty!(de.https.per_ip_counts)
    finally
        unlock(de.lock)
    end
end

function process_packet!(de::DetectionEngine, ev::PacketEvent, logger::Logger)
    lock(de.lock)
    try
        push_event!(de.window, ev)

        # DoS: count per source IP
        de.dos.per_ip_counts[ev.src_ip] = get(de.dos.per_ip_counts, ev.src_ip, 0) + 1
        if de.dos.per_ip_counts[ev.src_ip] >= de.dos.threshold
            alert = DetectionAlert(now(), "DoS", :high, ev.src_ip,
                "Single-IP packet rate $(de.dos.per_ip_counts[ev.src_ip]) >= $(de.dos.threshold)")
            push!(de.dos.alerts, alert)
            push!(de.all_alerts, alert)
            @logwarn logger "DoS ALERT: $(alert.src_ip) rate=$(de.dos.per_ip_counts[ev.src_ip])"
            de.dos.per_ip_counts[ev.src_ip] = 0
        end

        # DDoS: aggregate
        de.ddos.total_count += 1
        push!(de.ddos.unique_ips, ev.src_ip)
        if de.ddos.total_count >= de.ddos.threshold_packets &&
           length(de.ddos.unique_ips) >= de.ddos.threshold_ips
            alert = DetectionAlert(now(), "DDoS", :critical, "MULTIPLE",
                "Total $(de.ddos.total_count) pkt/s from $(length(de.ddos.unique_ips)) unique IPs")
            push!(de.ddos.alerts, alert)
            push!(de.all_alerts, alert)
            @logerror logger "DDoS ALERT: $(alert.detail)"
            de.ddos.total_count = 0
            empty!(de.ddos.unique_ips)
        end

        # HTTP flood
        if ev.protocol == :http
            de.http.per_ip_counts[ev.src_ip] = get(de.http.per_ip_counts, ev.src_ip, 0) + 1
            if de.http.per_ip_counts[ev.src_ip] >= de.http.threshold
                alert = DetectionAlert(now(), "HTTP_Flood", :high, ev.src_ip,
                    "HTTP req rate $(de.http.per_ip_counts[ev.src_ip]) >= $(de.http.threshold)")
                push!(de.http.alerts, alert)
                push!(de.all_alerts, alert)
                @logwarn logger "HTTP Flood: $(alert.src_ip) rate=$(de.http.per_ip_counts[ev.src_ip])"
                de.http.per_ip_counts[ev.src_ip] = 0
            end
        end

        # HTTPS flood
        if ev.protocol == :https
            de.https.per_ip_counts[ev.src_ip] = get(de.https.per_ip_counts, ev.src_ip, 0) + 1
            if de.https.per_ip_counts[ev.src_ip] >= de.https.threshold
                alert = DetectionAlert(now(), "HTTPS_Flood", :high, ev.src_ip,
                    "HTTPS req rate $(de.https.per_ip_counts[ev.src_ip]) >= $(de.https.threshold)")
                push!(de.https.alerts, alert)
                push!(de.all_alerts, alert)
                @logwarn logger "HTTPS Flood: $(alert.src_ip) rate=$(de.https.per_ip_counts[ev.src_ip])"
                de.https.per_ip_counts[ev.src_ip] = 0
            end
        end
    finally
        unlock(de.lock)
    end
end

# ============================================================================
# SECTION 7: TRAFFIC STATISTICS
# ============================================================================

mutable struct TrafficStats
    total_packets::Int
    total_bytes::Int
    proto_counts::Dict{Symbol,Int}
    top_src::Dict{String,Int}
    lock::ReentrantLock
end

TrafficStats() = TrafficStats(0, 0, Dict{Symbol,Int}(), Dict{String,Int}(), ReentrantLock())

function record!(ts::TrafficStats, ev::PacketEvent)
    lock(ts.lock)
    try
        ts.total_packets += 1
        ts.total_bytes += ev.size
        ts.proto_counts[ev.protocol] = get(ts.proto_counts, ev.protocol, 0) + 1
        ts.top_src[ev.src_ip] = get(ts.top_src, ev.src_ip, 0) + 1
    finally
        unlock(ts.lock)
    end
end

function top_talkers(ts::TrafficStats, k::Int=10)
    lock(ts.lock)
    try
        items = collect(ts.top_src)
        sort!(items, by=x->x[2], rev=true)
        return items[1:min(k, length(items))]
    finally
        unlock(ts.lock)
    end
end

# ============================================================================
# SECTION 8: TRAFFIC SIMULATION
# ============================================================================

mutable struct TrafficSimulator
    running::Bool
    task::Union{Nothing, Task}
    attacker_pool::Vector{String}
    victim_pool::Vector{String}
    rng::MersenneTwister
end

TrafficSimulator() = TrafficSimulator(false, nothing, String[], String[], MersenneTwister(42))

function seed_pools!(sim::TrafficSimulator)
    sim.attacker_pool = ["10.0.0.$i" for i in 1:50]
    sim.victim_pool   = ["192.168.1.$(i)" for i in 1:20]
end

function random_packet!(sim::TrafficSimulator)::PacketEvent
    if isempty(sim.attacker_pool)
        seed_pools!(sim)
    end
    r = rand(sim.rng)
    src = rand(sim.rng, sim.attacker_pool)
    dst = rand(sim.rng, sim.victim_pool)
    proto = :tcp
    sport = rand(sim.rng, 1024:65535)
    dport = 80
    size = rand(sim.rng, 64:1500)
    flags = "SYN"

    if r < 0.55
        proto = :tcp
        dport = rand(sim.rng, [80, 443, 22, 8080])
    elseif r < 0.75
        proto = :udp
        dport = rand(sim.rng, [53, 123, 161])
        flags = ""
    elseif r < 0.85
        proto = :icmp
        dport = 0
        flags = ""
    elseif r < 0.95
        proto = :http
        dport = 80
        flags = "GET"
    else
        proto = :https
        dport = 443
        flags = "TLS"
    end
    return PacketEvent(now(), src, dst, sport, dport, proto, size, flags)
end

function start_simulation!(sim::TrafficSimulator, engine::DetectionEngine,
                           stats::TrafficStats, logger::Logger,
                           pkt_per_sec::Int=200)
    if sim.running
        @logwarn logger "Simulator already running."
        return
    end
    seed_pools!(sim)
    sim.running = true
    sim.task = @async begin
        @loginfo logger "Traffic simulator started at ~$pkt_per_sec pkt/s"
        interval = 1.0 / pkt_per_sec
        while sim.running
            ev = random_packet!(sim)
            record!(stats, ev)
            process_packet!(engine, ev, logger)
            sleep(interval)
        end
        @loginfo logger "Traffic simulator stopped."
    end
end

function stop_simulation!(sim::TrafficSimulator, logger::Logger)
    sim.running = false
    @loginfo logger "Stopping simulator..."
end

# ============================================================================
# SECTION 9: PERSISTENCE
# ============================================================================

function save_blockchain(bc::IPBlockchain, path::String)
    open(path, "w") do io
        for blk in bc.chain
            println(io, "BLOCK|$(blk.index)|$(blk.timestamp)|$(blk.previous_hash)|$(blk.nonce)|$(blk.hash)")
            for r in blk.data
                println(io, "IP|$(r.ip)|$(r.added_at)|$(r.added_by)|$(r.note)")
            end
            println(io, "END")
        end
    end
end

function load_blockchain(path::String)::Union{Nothing, IPBlockchain}
    if !isfile(path)
        return nothing
    end
    bc = IPBlockchain()
    empty!(bc.chain)
    empty!(bc.ip_index)

    cur_index = -1
    cur_ts = now()
    cur_prev = GENESIS_HASH
    cur_nonce = 0
    cur_hash = ""
    cur_data = IPRecord[]

    for line in eachline(path)
        parts = split(line, "|")
        if length(parts) >= 6 && parts[1] == "BLOCK"
            cur_index = parse(Int, parts[2])
            cur_ts = DateTime(parts[3])
            cur_prev = parts[4]
            cur_nonce = parse(Int, parts[5])
            cur_hash = parts[6]
            cur_data = IPRecord[]
        elseif length(parts) >= 5 && parts[1] == "IP"
            push!(cur_data, IPRecord(parts[2], DateTime(parts[3]), parts[4], parts[5]))
        elseif parts[1] == "END"
            blk = IPBlock(cur_index, cur_ts, cur_prev, cur_data, cur_nonce, cur_hash)
            push!(bc.chain, blk)
            for r in cur_data
                bc.ip_index[r.ip] = blk.index
            end
        end
    end
    return length(bc.chain) > 0 ? bc : nothing
end

# ============================================================================
# SECTION 10: BULK IP GENERATOR
# ============================================================================

function generate_bulk_ips(n::Int, base::String="10.1.0.0")::Vector{String}
    ips = String[]
    parts = split(base, ".")
    if length(parts) != 4
        error("Base must be IPv4 dotted quad")
    end
    o1 = parse(Int, parts[1])
    o2 = parse(Int, parts[2])
    o3 = parse(Int, parts[3])
    counter = 0
    i = 0
    while counter < n && i < 65536
        o4 = i % 256
        o3x = o3 + (i ÷ 256)
        if o3x > 255
            o2x = o2 + (o3x ÷ 256)
            o3x = o3x % 256
        else
            o2x = o2
        end
        ip = "$o1.$o2x.$o3x.$o4"
        if is_valid_ip(ip)
            push!(ips, ip)
            counter += 1
        end
        i += 1
    end
    return ips
end

# ============================================================================
# SECTION 11: BLOCK LIST
# ============================================================================

mutable struct BlockList
    blocked::Set{String}
    reasons::Dict{String,String}
    lock::ReentrantLock
end

BlockList() = BlockList(Set{String}(), Dict{String,String}(), ReentrantLock())

function block_ip!(bl::BlockList, ip::String, reason::String, logger::Logger)
    lock(bl.lock)
    try
        push!(bl.blocked, normalize_ip(ip))
        bl.reasons[normalize_ip(ip)] = reason
        @logwarn logger "Blocked IP $ip ($reason)"
    finally
        unlock(bl.lock)
    end
end

function unblock_ip!(bl::BlockList, ip::String, logger::Logger)
    lock(bl.lock)
    try
        delete!(bl.blocked, normalize_ip(ip))
        delete!(bl.reasons, normalize_ip(ip))
        @loginfo logger "Unblocked IP $ip"
    finally
        unlock(bl.lock)
    end
end

function is_blocked(bl::BlockList, ip::String)::Bool
    lock(bl.lock)
    try
        return in(normalize_ip(ip), bl.blocked)
    finally
        unlock(bl.lock)
    end
end

# ============================================================================
# SECTION 12: CONTROL INTERFACE (REPL)
# ============================================================================

mutable struct App
    blockchain::IPBlockchain
    engine::DetectionEngine
    stats::TrafficStats
    simulator::TrafficSimulator
    blocklist::BlockList
    logger::Logger
    save_path::String
    running::Bool
end

function App(; logpath::Union{Nothing,String}=nothing,
             save_path::String="hermitcrab_chain.dat")
    App(
        IPBlockchain(),
        DetectionEngine(),
        TrafficStats(),
        TrafficSimulator(),
        BlockList(),
        Logger(:info, logpath),
        save_path,
        true
    )
end

function print_banner()
    println("""
    ==============================================================
    |                                                            |
    |        HERMIT-CRAB  -  v$(APP_VERSION)                       |
    |   Blockchain IP Storage & DDoS/DoS/Flood Detection         |
    |                                                            |
    ==============================================================
    """)
end

function print_help()
    println("""
    Commands:
      help                          Show this help
      add <ip>[,<ip>...]            Add IP(s) to blockchain
      addfile <path>                Add IPs from a file (one per line)
      bulk <n> [base]               Generate & add n IPs from base (default 10.1.0.0)
      list                          List all IPs in the blockchain
      exists <ip>                   Check if IP exists in chain
      stats                         Show blockchain statistics
      chain                         Print full block info (summary)
      validate                      Verify chain integrity
      save [path]                   Save blockchain to disk
      load <path>                   Load blockchain from disk

      sim start [rate]              Start traffic simulator (default 200 pkt/s)
      sim stop                      Stop simulator
      sim burst <n> <pps>           Generate n bursts of high-rate traffic

      top [k]                       Show top-k talkers
      alerts [k]                    Show last k alerts (default 20)
      reset                         Reset detection counters
      clearalerts                   Clear alert history

      block <ip> [reason]           Add IP to blocklist
      unblock <ip>                  Remove IP from blocklist
      blocked                       List blocked IPs

      config                        Show current configuration
      set <key> <value>             Modify config

      quit | exit                   Exit
    """)
end

function print_stats(bc::IPBlockchain)
    s = chain_stats(bc)
    println("+-- Blockchain Statistics ------------------------")
    println("| Blocks          : $(s["blocks"])")
    println("| Unique IPs      : $(s["unique_ips"])")
    println("| Chain valid     : $(s["valid"])")
    println("| Last hash       : $(s["last_hash"])")
    println("+------------------------------------------------")
end

function print_chain(bc::IPBlockchain)
    lock(bc.lock)
    try
        println("+-- Chain (", length(bc.chain), " blocks) --")
        for blk in bc.chain
            println("| Block #$(blk.index)  ts=$(blk.timestamp)")
            println("|   prev=$(blk.previous_hash[1:min(16, end)])...")
            println("|   hash=$(blk.hash[1:min(16, end)])...  nonce=$(blk.nonce)")
            println("|   ips =$(length(blk.data))")
            for r in blk.data
                println("|      - $(r.ip)  [$(r.note)]")
            end
        end
        println("+------------------------------------------")
    finally
        unlock(bc.lock)
    end
end

function print_top(stats::TrafficStats, k::Int)
    println("+-- Top $k Talkers --")
    for (ip, c) in top_talkers(stats, k)
        println("| $ip  ->  $c packets")
    end
    println("+--------------------")
end

function print_alerts(engine::DetectionEngine, k::Int)
    lock(engine.lock)
    try
        n = length(engine.all_alerts)
        start = max(1, n - k + 1)
        println("+-- Last $(min(k,n)) of $n alerts --")
        for i in start:n
            a = engine.all_alerts[i]
            println("| [$(a.timestamp)] $(a.alert_type) ($(a.severity)) src=$(a.src_ip)")
            println("|    $(a.detail)")
        end
        println("+------------------------------------")
    finally
        unlock(engine.lock)
    end
end

function print_config(engine::DetectionEngine)
    println("+-- Configuration --")
    println("| DoS threshold       : $(engine.dos.threshold) pkt")
    println("| DDoS packet thresh  : $(engine.ddos.threshold_packets) pkt")
    println("| DDoS unique-IP th.  : $(engine.ddos.threshold_ips) IPs")
    println("| HTTP flood thresh   : $(engine.http.threshold) req")
    println("| HTTPS flood thresh  : $(engine.https.threshold) req")
    println("| Monitor window      : $(engine.window.window_sec) s")
    println("+--------------------")
end

function handle_command(app::App, line::String)
    parts = split(strip(line))
    isempty(parts) && return
    cmd = lowercase(parts[1])

    if cmd == "help"
        print_help()
    elseif cmd == "add"
        if length(parts) < 2
            println("usage: add <ip>[,<ip>...]")
            return
        end
        joined = join(parts[2:end], " ")
        ips = parse_ip_list(joined)
        n = add_ips!(app.blockchain, ips, "cli-user", "manual add", app.logger)
        println("Added $n IP(s) to blockchain.")
    elseif cmd == "addfile"
        if length(parts) < 2
            println("usage: addfile <path>")
            return
        end
        path = parts[2]
        if !isfile(path)
            println("File not found: $path")
            return
        end
        ips = String[]
        for l in eachline(path)
            t = strip(l)
            if !isempty(t) && is_valid_ip(t)
                push!(ips, t)
            end
        end
        n = add_ips!(app.blockchain, ips, "cli-user", "file add", app.logger)
        println("Added $n IP(s) from file.")
    elseif cmd == "bulk"
        if length(parts) < 2
            println("usage: bulk <n> [base]")
            return
        end
        n = parse(Int, parts[2])
        base = length(parts) >= 3 ? parts[3] : "10.1.0.0"
        ips = generate_bulk_ips(n, base)
        added = add_ips!(app.blockchain, ips, "cli-user", "bulk gen", app.logger)
        println("Generated $n IPs, added $added to blockchain.")
    elseif cmd == "list"
        ips = list_ips(app.blockchain)
        println("Total IPs: ", length(ips))
        for r in ips
            println("  ", r.ip, "  [", r.note, "]  ", r.added_at)
        end
    elseif cmd == "exists"
        if length(parts) < 2
            println("usage: exists <ip>")
            return
        end
        println(ip_exists(app.blockchain, parts[2]) ? "YES" : "NO")
    elseif cmd == "stats"
        print_stats(app.blockchain)
    elseif cmd == "chain"
        print_chain(app.blockchain)
    elseif cmd == "validate"
        println(is_chain_valid(app.blockchain) ? "Chain VALID" : "Chain INVALID")
    elseif cmd == "save"
        path = length(parts) >= 2 ? parts[2] : app.save_path
        save_blockchain(app.blockchain, path)
        println("Saved to $path")
    elseif cmd == "load"
        if length(parts) < 2
            println("usage: load <path>")
            return
        end
        bc = load_blockchain(parts[2])
        if bc === nothing
            println("Failed to load.")
        else
            app.blockchain = bc
            println("Loaded $(length(bc.chain)) blocks, $(length(bc.ip_index)) IPs.")
        end
    elseif cmd == "sim"
        if length(parts) < 2
            println("usage: sim start [rate] | sim stop | sim burst <n> <pps>")
            return
        end
        sub = lowercase(parts[2])
        if sub == "start"
            rate = length(parts) >= 3 ? parse(Int, parts[3]) : 200
            start_simulation!(app.simulator, app.engine, app.stats, app.logger, rate)
            println("Simulator started at $rate pkt/s")
        elseif sub == "stop"
            stop_simulation!(app.simulator, app.logger)
            println("Simulator stopped.")
        elseif sub == "burst"
            if length(parts) < 4
                println("usage: sim burst <n> <pps>")
                return
            end
            n = parse(Int, parts[3])
            pps = parse(Int, parts[4])
            @async begin
                for i in 1:n
                    interval = 1.0 / pps
                    for _ in 1:pps
                        ev = random_packet!(app.simulator)
                        record!(app.stats, ev)
                        process_packet!(app.engine, ev, app.logger)
                        sleep(interval)
                    end
                    println("burst $i/$n done")
                end
            end
            println("Launched $n bursts @ $pps pkt/s")
        else
            println("Unknown sim subcommand.")
        end
    elseif cmd == "top"
        k = length(parts) >= 2 ? parse(Int, parts[2]) : 10
        print_top(app.stats, k)
    elseif cmd == "alerts"
        k = length(parts) >= 2 ? parse(Int, parts[2]) : 20
        print_alerts(app.engine, k)
    elseif cmd == "reset"
        reset_counters!(app.engine)
        println("Detection counters reset.")
    elseif cmd == "clearalerts"
        lock(app.engine.lock)
        try
            empty!(app.engine.all_alerts)
            empty!(app.engine.dos.alerts)
            empty!(app.engine.ddos.alerts)
            empty!(app.engine.http.alerts)
            empty!(app.engine.https.alerts)
        finally
            unlock(app.engine.lock)
        end
        println("Alerts cleared.")
    elseif cmd == "block"
        if length(parts) < 2
            println("usage: block <ip> [reason]")
            return
        end
        reason = length(parts) >= 3 ? join(parts[3:end], " ") : "manual"
        block_ip!(app.blocklist, parts[2], reason, app.logger)
        println("Blocked $(parts[2]).")
    elseif cmd == "unblock"
        if length(parts) < 2
            println("usage: unblock <ip>")
            return
        end
        unblock_ip!(app.blocklist, parts[2], app.logger)
        println("Unblocked $(parts[2]).")
    elseif cmd == "blocked"
        lock(app.blocklist.lock)
        try
            println("Blocked IPs: ", length(app.blocklist.blocked))
            for ip in app.blocklist.blocked
                println("  $ip  ($(app.blocklist.reasons[ip]))")
            end
        finally
            unlock(app.blocklist.lock)
        end
    elseif cmd == "config"
        print_config(app.engine)
    elseif cmd == "set"
        if length(parts) < 3
            println("usage: set <key> <value>")
            return
        end
        key = lowercase(parts[2])
        val = tryparse(Int, parts[3])
        if val === nothing
            println("Value must be integer.")
            return
        end
        if key == "dos_threshold"
            app.engine.dos.threshold = val
        elseif key == "ddos_threshold"
            app.engine.ddos.threshold_packets = val
        elseif key == "http_threshold"
            app.engine.http.threshold = val
        elseif key == "https_threshold"
            app.engine.https.threshold = val
        elseif key == "window"
            app.engine.window.window_sec = val
        else
            println("Unknown key.")
            return
        end
        println("Set $key = $val")
    elseif cmd == "quit" || cmd == "exit"
        app.running = false
    else
        println("Unknown command. Type 'help'.")
    end
end

function repl(app::App)
    print_banner()
    println("Type 'help' for commands.\n")
    while app.running
        print("hermit-crab-v1> ")
        flush(stdout)
        line = try
            readline()
        catch
            break
        end
        try
            handle_command(app, line)
        catch e
            println("Error: ", e)
        end
    end
    try
        save_blockchain(app.blockchain, app.save_path)
        println("\nBlockchain saved to $(app.save_path). Goodbye.")
    catch e
        println("Failed to save: ", e)
    end
end

# ============================================================================
# SECTION 13: SELF-TEST
# ============================================================================

function self_test()
    println("Running self-test...")
    @assert is_valid_ip("192.168.1.1")
    @assert is_valid_ip("::1")
    @assert !is_valid_ip("999.999.999.999")

    bc = IPBlockchain()
    @assert length(bc.chain) == 1
    @assert is_chain_valid(bc)

    logger = Logger(:error)
    n = add_ips!(bc, ["10.0.0.1", "10.0.0.2", "10.0.0.3"], "test", "selftest", logger)
    @assert n == 3
    @assert is_chain_valid(bc)
    @assert ip_exists(bc, "10.0.0.1")
    @assert !ip_exists(bc, "10.0.0.99")

    engine = DetectionEngine()
    stats = TrafficStats()
    for i in 1:150
        ev = PacketEvent(now(), "1.1.1.1", "2.2.2.2", 1234, 80, :tcp, 100, "SYN")
        record!(stats, ev)
        process_packet!(engine, ev, logger)
    end
    @assert length(engine.dos.alerts) >= 1

    ips = generate_bulk_ips(500)
    @assert length(ips) == 500

    println("All self-tests PASSED.")
end

# ============================================================================
# SECTION 14: MAIN ENTRY
# ============================================================================

function main(args::Vector{String})
    if "--selftest" in args
        self_test()
        return
    end

    logpath = "--log" in args ? "hermit-crab.log" : nothing
    app = App(logpath=logpath)

    if isfile(app.save_path)
        bc = load_blockchain(app.save_path)
        if bc !== nothing
            app.blockchain = bc
            @loginfo app.logger "Preloaded $(length(bc.chain)) blocks from $(app.save_path)"
        end
    end

    repl(app)
end

end # module HermitCrabV1

# ============================================================================
# ENTRY POINT
# ============================================================================

if abspath(PROGRAM_FILE) == @__FILE__
    HermitCrabV1.main(ARGS)
end
