package mara

import "core:fmt"
import "core:time"

MAX_PERF_PHASES :: 16

Performance_Timer :: struct {
    names:       [MAX_PERF_PHASES]string,
    times:       [MAX_PERF_PHASES]f64,      // Duration in seconds
    count:       int,
    phase_start: time.Time,                  // Start of current phase
    total_start: time.Time,                  // Start of entire timing session
    quiet:       bool,                       // suppress all printing (e.g. `mara ask` keeps stdout clean)
}

// Begin timing session - call once at the start. Prints the header so
// per-phase lines from subsequent marks stream under it.
perf_timer_begin :: proc(timer: ^Performance_Timer, first_phase: string) {
    timer.count = 0
    timer.total_start = time.now()
    timer.phase_start = timer.total_start
    timer.names[0] = first_phase
    if !timer.quiet { fmt.println("=== Performance ===") }
}

// End current phase and start a new one - single call per phase transition.
// Records the time for the previous phase, prints it, then starts the next.
perf_timer_mark :: proc(timer: ^Performance_Timer, next_phase: string) {
    now := time.now()

    // Record time for the phase that just ended
    if timer.count < MAX_PERF_PHASES {
        elapsed := time.duration_seconds(time.diff(timer.phase_start, now))
        timer.times[timer.count] = elapsed
        if !timer.quiet { fmt.printf("  %s: %.1fms\n", timer.names[timer.count], elapsed * 1000) }
        timer.count += 1
    }

    // Start timing the new phase
    if timer.count < MAX_PERF_PHASES {
        timer.names[timer.count] = next_phase
    }
    timer.phase_start = now
}

// End the final phase and print the total. The final phase's own line
// streams from here too, then the cumulative total.
perf_timer_end :: proc(timer: ^Performance_Timer) {
    now := time.now()

    // Record + print the final phase
    if timer.count < MAX_PERF_PHASES {
        elapsed := time.duration_seconds(time.diff(timer.phase_start, now))
        timer.times[timer.count] = elapsed
        if !timer.quiet { fmt.printf("  %s: %.1fms\n", timer.names[timer.count], elapsed * 1000) }
        timer.count += 1
    }

    if timer.quiet { return }
    total := time.duration_seconds(time.diff(timer.total_start, now))
    fmt.printf("  Total: %.1fms\n", total * 1000)
    // Closing divider — same width as "=== Performance ===" (19 chars).
    // Visually wraps the timer block so diagnostic flushes and the
    // success message that follow read as separate.
    fmt.println("===================")
}

// Get time for a specific phase by index
perf_timer_get :: proc(timer: ^Performance_Timer, index: int) -> f64 {
    if index < 0 || index >= timer.count {
        return 0
    }
    return timer.times[index]
}

// Get total time
perf_timer_total :: proc(timer: ^Performance_Timer) -> f64 {
    if timer.count == 0 {
        return 0
    }
    total: f64 = 0
    for i in 0..<timer.count {
        total += timer.times[i]
    }
    return total
}
