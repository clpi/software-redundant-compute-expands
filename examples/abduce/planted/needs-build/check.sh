#!/bin/sh
# planted control for prerequisite abduction: fails on a fresh tree until the build has run
test "$(tail -1 gen/table.txt 2>/dev/null)" = "64 2080" || { echo "table check failed"; exit 1; }
echo ok
