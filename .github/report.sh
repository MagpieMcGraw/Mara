# Sourced at the start of a workflow step: what the step says is kept, and
# shown at its end; when it fails, its last lines are also an error
# annotation, which the run's page shows to anyone, signed in or not.
exec 3>&1 > "$RUNNER_TEMP/step.txt" 2>&1
report() {
    rc=$?
    { set +x; } 2> /dev/null
    cat "$RUNNER_TEMP/step.txt" >&3
    if [ "$rc" != 0 ]; then
        text=$(tail -c 3000 "$RUNNER_TEMP/step.txt" | sed -z 's/%/%25/g; s/\r//g; s/\n/%0A/g')
        echo "::error title=$GITHUB_JOB failed::$text" >&3
    fi
}
trap report EXIT
set -x
