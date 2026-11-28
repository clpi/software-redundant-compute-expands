#!/bin/sh
# planted control: not idempotent from a clean tree (the first run only warms a cache)
if [ ! -f .cache/warm ]; then mkdir -p .cache && echo warmed > .cache/warm && echo "cold start" && exit 1; fi
echo ok
