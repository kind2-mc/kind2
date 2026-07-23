#!/usr/bin/env bash

#########################################################################
# This file is part of the Kind 2 model checker.                        #
#                                                                       #
# Copyright (c) 2024 by the Board of Trustees of the University of Iowa #
#                                                                       #
# Licensed under the Apache License, Version 2.0 (the "License"); you   #
# may not use this file except in compliance with the License.  You     #
# may obtain a copy of the License at                                   #
#                                                                       #
# http://www.apache.org/licenses/LICENSE-2.0                            #
#                                                                       #
# Unless required by applicable law or agreed to in writing, software   #
# distributed under the License is distributed on an "AS IS" BASIS,     #
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or       #
# implied. See the License for the specific language governing          #
# permissions and limitations under the License.                        #
#########################################################################

# Run a single Kind 2 binary over every *.lus file under one or more benchmark
# directories, sequentially, and write a stat file with one line per benchmark:
#
#     <relative/path.lus> <Result> <wall_seconds>
#
# where <Result> is one of Valid, Invalid, Timeout, Error, Mixed. The relative
# path is taken with respect to <bench_root>, so selecting several subdirs of a
# common root yields distinct, stable names (e.g. Bool/x.lus, Int/y.lus).
#
# This replaces the cluster's TreeLimitedRun + run-benchmark.sh + benchmark-stat
# trio: we rely on Kind 2's own --timeout_wall for the soft limit, wrap it in
# `timeout` as a hard kill, and classify the output using the same distinguished
# strings benchmark-stat used for the "kind-2" profile.
#
# Usage:
#   run-benchmarks.sh <kind2_bin> <timeout_seconds> <out_stat> <bench_root> [subdir...]
#
# If no subdir is given, all *.lus under <bench_root> are run.
# Extra Kind 2 flags can be passed via the KIND2_EXTRA_ARGS environment variable.

set -u

if [ "$#" -lt 4 ]; then
  echo "Usage: $(basename "$0") <kind2_bin> <timeout_seconds> <out_stat> <bench_root> [subdir...]" >&2
  exit 2
fi

KIND2_BIN=$1
TIMEOUT=$2
OUT_STAT=$3
BENCH_ROOT=$4
shift 4
SUBDIRS=("$@")

# Optional extra Kind 2 flags (space-separated) via the environment.
read -r -a EXTRA_ARGS <<< "${KIND2_EXTRA_ARGS:-}"

if [ ! -x "$KIND2_BIN" ]; then
  echo "ERROR: Kind 2 binary '$KIND2_BIN' not found or not executable." >&2
  exit 2
fi
if [ ! -d "$BENCH_ROOT" ]; then
  echo "ERROR: benchmark root '$BENCH_ROOT' does not exist." >&2
  exit 2
fi

# Directories to search: each given subdir under the root, or the whole root.
SEARCH_DIRS=()
if [ "${#SUBDIRS[@]}" -eq 0 ]; then
  SEARCH_DIRS=("$BENCH_ROOT")
else
  for sub in "${SUBDIRS[@]}"; do
    d="$BENCH_ROOT/$sub"
    if [ ! -d "$d" ]; then
      echo "ERROR: benchmark subdir '$d' does not exist." >&2
      exit 2
    fi
    SEARCH_DIRS+=("$d")
  done
fi

# Distinguished strings, matching benchmark-stat's "kind-2" profile. With
# `--color false`, Kind 2 emits these tags verbatim at the start of a line.
VALID_PAT='^<Success> Property'
INVALID_PAT='^<Failure>'
ERROR_PAT='^<Error>'

# Hard kill a bit after Kind 2's own wall-clock timeout, in case it fails to
# stop itself (e.g. a wedged solver child process).
HARD_TIMEOUT=$((TIMEOUT + 15))

: > "$OUT_STAT"

# Deterministic ordering so head/base stat files line up and diffs are stable.
mapfile -t FILES < <(find "${SEARCH_DIRS[@]}" -type f -iname '*.lus' | sort)

# Optional round-robin sharding so several jobs can split the set. With
# SHARD_COUNT>1, this job runs only the files whose position in the sorted list
# satisfies (position mod SHARD_COUNT == SHARD_INDEX). Round-robin spreads
# adjacent (often similarly hard) benchmarks across shards for balance.
# SHARD_COUNT<=1 (the default) runs everything.
SHARD_COUNT=${SHARD_COUNT:-1}
SHARD_INDEX=${SHARD_INDEX:-0}
if [ "$SHARD_COUNT" -gt 1 ]; then
  mapfile -t FILES < <(printf '%s\n' "${FILES[@]}" \
    | awk -v n="$SHARD_COUNT" -v k="$SHARD_INDEX" 'NR % n == k')
fi

# When sharding, tag each stat line with this shard's index (4th column) so the
# comparison can point at the job whose log holds an errored benchmark's output.
if [ "$SHARD_COUNT" -gt 1 ]; then shard_field=" $SHARD_INDEX"; else shard_field=""; fi

total=${#FILES[@]}
if [ "$total" -eq 0 ]; then
  echo "ERROR: no *.lus benchmarks found under: ${SEARCH_DIRS[*]} (shard ${SHARD_INDEX}/${SHARD_COUNT})" >&2
  exit 2
fi

echo "Running $total benchmark(s) with '$KIND2_BIN' (timeout ${TIMEOUT}s)"

out_file=$(mktemp)
trap 'rm -f "$out_file"' EXIT

i=0
for f in "${FILES[@]}"; do
  i=$((i + 1))
  rel=${f#"$BENCH_ROOT"/}

  start=$(date +%s.%N)
  timeout "$HARD_TIMEOUT" "$KIND2_BIN" -v --color false \
    --timeout_wall "$TIMEOUT" "${EXTRA_ARGS[@]}" "$f" > "$out_file" 2>&1
  end=$(date +%s.%N)
  wall=$(awk "BEGIN { printf \"%.2f\", $end - $start }")

  # grep -c prints a count and exits 1 when there are no matches; that is fine,
  # we only read the printed count and never rely on the exit status.
  n_valid=$(grep -c "$VALID_PAT" "$out_file")
  n_invalid=$(grep -c "$INVALID_PAT" "$out_file")
  n_error=$(grep -c "$ERROR_PAT" "$out_file")

  if   [ "$n_error"   -gt 0 ]; then res=Error
  elif [ "$n_valid"   -gt 0 ] && [ "$n_invalid" -eq 0 ]; then res=Valid
  elif [ "$n_invalid" -gt 0 ] && [ "$n_valid"   -eq 0 ]; then res=Invalid
  elif [ "$n_valid"   -eq 0 ] && [ "$n_invalid" -eq 0 ]; then res=Timeout
  else res=Mixed
  fi

  printf '%s %s %s%s\n' "$rel" "$res" "$wall" "$shard_field" >> "$OUT_STAT"
  printf '[%d/%d] %-8s %6ss  %s\n' "$i" "$total" "$res" "$wall" "$rel"

  # Surface the Kind 2 output for errored benchmarks so "see logs" is actionable.
  # `::group::`/`::endgroup::` make it a collapsible section in the CI job log
  # (and are harmless plain text elsewhere).
  if [ "$res" = "Error" ]; then
    echo "::group::Kind 2 output for errored benchmark: $rel"
    cat "$out_file"
    echo "::endgroup::"
  fi
done

echo "Wrote $OUT_STAT"
