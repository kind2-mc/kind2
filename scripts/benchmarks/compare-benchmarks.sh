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

# Compare two stat files produced by run-benchmarks.sh (PR head vs. base),
# write a Markdown summary (to $GITHUB_STEP_SUMMARY when running in CI), and
# exit non-zero when the head introduces a regression or a soundness bug.
#
# The comparison mirrors the cluster's test_pr logic:
#   - Soundness bug:  base = Invalid  ->  head = Valid          (exit 2)
#   - Regression:     base = Valid    ->  head != Valid/Timeout (exit 1)
#                     base = Invalid  ->  head != Invalid/Timeout (exit 1)
# A head Timeout where the base solved the benchmark is NOT treated as a
# regression (timing on shared CI runners is noisy); it is reported for
# information only.
#
# Usage:
#   compare-benchmarks.sh <head_stat> <base_stat> [summary_file]

set -u

if [ "$#" -lt 2 ]; then
  echo "Usage: $(basename "$0") <head_stat> <base_stat> [summary_file]" >&2
  exit 3
fi

HEAD_STAT=$1
BASE_STAT=$2
SUMMARY=${3:-/dev/stdout}

for f in "$HEAD_STAT" "$BASE_STAT"; do
  if [ ! -f "$f" ]; then
    echo "ERROR: stat file '$f' does not exist." >&2
    exit 3
  fi
done

emit() { printf '%s\n' "$*" >> "$SUMMARY"; }

# Sort by benchmark name so `join` lines up head and base rows.
sort -k1,1 -o "$HEAD_STAT" "$HEAD_STAT"
sort -k1,1 -o "$BASE_STAT" "$BASE_STAT"

joined=$(mktemp)
trap 'rm -f "$joined"' EXIT
# Output columns: name headRes headWall baseRes baseWall
join -j1 "$HEAD_STAT" "$BASE_STAT" > "$joined"

n_head=$(wc -l < "$HEAD_STAT")
n_base=$(wc -l < "$BASE_STAT")
n_common=$(wc -l < "$joined")

regressions=()
soundness=()
improvements=()
head_total=0
base_total=0

while read -r name hr hw br bw; do
  head_total=$(awk "BEGIN { printf \"%.2f\", $head_total + $hw }")
  base_total=$(awk "BEGIN { printf \"%.2f\", $base_total + $bw }")

  if [ "$br" = "Invalid" ] && [ "$hr" = "Valid" ]; then
    soundness+=("$name|$br|$hr")
  elif [ "$br" = "Valid" ] && [ "$hr" != "Valid" ] && [ "$hr" != "Timeout" ]; then
    regressions+=("$name|$br|$hr")
  elif [ "$br" = "Invalid" ] && [ "$hr" != "Invalid" ] && [ "$hr" != "Timeout" ]; then
    regressions+=("$name|$br|$hr")
  elif [ "$br" = "Timeout" ] && { [ "$hr" = "Valid" ] || [ "$hr" = "Invalid" ]; }; then
    improvements+=("$name|$br|$hr")
  fi
done < "$joined"

# ---- Overall verdict & exit code -------------------------------------------
if [ "${#soundness[@]}" -gt 0 ]; then
  verdict=":x: **Soundness bug** — the PR reports a property Valid that the base found Invalid."
  exit_code=2
elif [ "${#regressions[@]}" -gt 0 ]; then
  verdict=":x: **Regression** — the PR changes ${#regressions[@]} result(s) for the worse."
  exit_code=1
else
  verdict=":white_check_mark: **No regressions** — the PR conforms with the base branch."
  exit_code=0
fi

# ---- Markdown report --------------------------------------------------------
emit "## Kind 2 benchmark comparison (PR head vs. base)"
emit ""
emit "$verdict"
emit ""
emit "| | Benchmarks | Total wall time |"
emit "|---|---:|---:|"
emit "| PR head | $n_head | ${head_total}s |"
emit "| Base    | $n_base | ${base_total}s |"
emit ""
if [ "$n_head" -ne "$n_common" ] || [ "$n_base" -ne "$n_common" ]; then
  emit "> :warning: Only $n_common benchmark(s) ran under **both** binaries; unmatched benchmarks are excluded from the comparison."
  emit ""
fi

emit_table() {
  # $1 = title, remaining args = "name|base|head" rows
  local title=$1; shift
  emit "### $title"
  if [ "$#" -eq 0 ]; then
    emit "_None._"
    emit ""
    return
  fi
  emit "| Benchmark | Base | PR head |"
  emit "|---|---|---|"
  local row
  for row in "$@"; do
    emit "| \`${row%%|*}\` | $(echo "$row" | cut -d'|' -f2) | $(echo "$row" | cut -d'|' -f3) |"
  done
  emit ""
}

if [ "${#soundness[@]}" -gt 0 ]; then
  emit_table ":rotating_light: Soundness bugs" "${soundness[@]}"
fi
emit_table "Regressions" "${regressions[@]}"
emit_table "Improvements (Timeout → solved)" "${improvements[@]}"

exit "$exit_code"
