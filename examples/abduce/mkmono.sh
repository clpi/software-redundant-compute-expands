#!/bin/sh
# MONO for the public run: this repository's first-parent history replayed under
# theses/redundant-compute-expands, so causes that read history (regression bisection,
# restoring a tracked file) have the commits to read.  Usage: mkmono.sh REPO MONO
set -eu
repo=$(cd "$1" && pwd); mono=$2
mkdir -p "$mono" && cd "$mono" && git init -q
d=theses/redundant-compute-expands
for c in $(git -C "$repo" rev-list --reverse --first-parent HEAD); do
  rm -rf "$d" && mkdir -p "$d"
  git -C "$repo" archive "$c" | tar -x -C "$d"
  git add -A
  GIT_AUTHOR_DATE=$(git -C "$repo" log -1 --format=%aI "$c") GIT_COMMITTER_DATE=$(git -C "$repo" log -1 --format=%cI "$c") \
    git -c user.email=a@b -c user.name=abduction commit -q --allow-empty -m "$(git -C "$repo" log -1 --format=%s "$c") [$c]"
done
