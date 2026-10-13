package mara

import "core:fmt"
import "core:time"

// The compile's phase timings, each printed as its phase ends.
Performance_Timer :: struct {
    phase:       string,      // the phase being timed
    phase_start: time.Time,
    total_start: time.Time,
    quiet:       bool,        // suppress all printing (e.g. `mara ask` keeps stdout clean)
}

// Begin timing - call once at the start. Prints the header so per-phase
// lines from subsequent marks stream under it.
perf_timer_begin :: proc(timer: ^Performance_Timer, first_phase: string) {
    timer.total_start = time.now()
    timer.phase_start = timer.total_start
    timer.phase = first_phase
    if !timer.quiet { fmt.println("=== Performance ===") }
}

// End the current phase (its line printed) and start the next.
perf_timer_mark :: proc(timer: ^Performance_Timer, next_phase: string) {
    now := time.now()
    perf_timer_print(timer, now)
    timer.phase, timer.phase_start = next_phase, now
}

// End the current phase but for `carried` of it — work done during it that
// is the next phase's (the middle end's analyses, run as each code is
// lowered) — and start the next with that much of it.
perf_timer_mark_carry :: proc(timer: ^Performance_Timer, next_phase: string, carried: time.Duration) {
    now := time.now()
    carried := min(carried, time.diff(timer.phase_start, now))   // (several workers' sum: at most the phase)
    timer.phase_start = time.time_add(timer.phase_start, carried)
    perf_timer_print(timer, now)
    timer.phase, timer.phase_start = next_phase, time.time_add(now, -carried)
}

// End the final phase and print the total.
perf_timer_end :: proc(timer: ^Performance_Timer) {
    now := time.now()
    perf_timer_print(timer, now)
    if timer.quiet { return }
    total := time.duration_seconds(time.diff(timer.total_start, now))
    fmt.printf("  Total: %.1fms\n", total * 1000)
    // Closing divider — same width as "=== Performance ===" (19 chars).
    // Visually wraps the timer block so diagnostic flushes and the
    // success message that follow read as separate.
    fmt.println("===================")
}

@(private="file")
perf_timer_print :: proc(timer: ^Performance_Timer, now: time.Time) {
    if timer.quiet { return }
    elapsed := time.duration_seconds(time.diff(timer.phase_start, now))
    fmt.printf("  %s: %.1fms\n", timer.phase, elapsed * 1000)
}
