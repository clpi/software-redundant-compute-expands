#!/bin/sh
# planted control for flaky gates: without gen/ok it fails about 3 runs in 4
[ -f gen/ok ] && { echo ok; exit 0; }
r=$(od -An -N1 -tu1 /dev/urandom | tr -d ' ')
[ $((r % 4)) -eq 0 ] && { echo "lucky"; exit 0; }
echo "race lost"; exit 1
