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
}

// Begin timing session - call once at the start
perf_timer_begin :: proc(timer: ^Performance_Timer, first_phase: string) {
    timer.count = 0
    timer.total_start = time.now()
    timer.phase_start = timer.total_start
    timer.names[0] = first_phase
}

// End current phase and start a new one - single call per phase transition
// Records the time for the previous phase and starts timing the new phase
perf_timer_mark :: proc(timer: ^Performance_Timer, next_phase: string) {
    now := time.now()

    // Record time for the phase that just ended
    if timer.count < MAX_PERF_PHASES {
        timer.times[timer.count] = time.duration_seconds(time.diff(timer.phase_start, now))
        timer.count += 1
    }

    // Start timing the new phase
    if timer.count < MAX_PERF_PHASES {
        timer.names[timer.count] = next_phase
    }
    timer.phase_start = now
}

// End the final phase and print results
perf_timer_end :: proc(timer: ^Performance_Timer) {
    now := time.now()

    // Record time for the final phase
    if timer.count < MAX_PERF_PHASES {
        timer.times[timer.count] = time.duration_seconds(time.diff(timer.phase_start, now))
        timer.count += 1
    }

    // Calculate total
    total := time.duration_seconds(time.diff(timer.total_start, now))

    // Print results
    fmt.println("=== Performance ===")
    for i in 0..<timer.count {
        fmt.printf("  %s: %.1fms\n", timer.names[i], timer.times[i] * 1000)
    }
    fmt.printf("  Total: %.1fms\n", total * 1000)
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
