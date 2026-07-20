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

# Head shard per benchmark, from the optional 4th column that sharded CI runs
# write (see run-benchmarks.sh). Lets the Errors table point at the job whose
# log holds an errored benchmark's output. Absent for unsharded/local runs.
declare -A head_shard
while read -r s_name _s_res _s_wall s_shard _rest; do
  [ -n "${s_shard:-}" ] && head_shard["$s_name"]="$s_shard"
done < "$HEAD_STAT"

# Normalize to <name result wall> so the join is robust to the extra column.
h3=$(mktemp); b3=$(mktemp); joined=$(mktemp)
trap 'rm -f "$h3" "$b3" "$joined"' EXIT
awk '{ print $1, $2, $3 }' "$HEAD_STAT" | sort -k1,1 > "$h3"
awk '{ print $1, $2, $3 }' "$BASE_STAT" | sort -k1,1 > "$b3"
# Output columns: name headRes headWall baseRes baseWall
join -j1 "$h3" "$b3" > "$joined"

n_head=$(wc -l < "$HEAD_STAT")
n_base=$(wc -l < "$BASE_STAT")
n_common=$(wc -l < "$joined")

# Per-category counts and total wall time, computed directly from each stat file.
count_cat() { awk -v c="$2" '$2 == c { n++ } END { print n + 0 }' "$1"; }
total_wall() { awk '{ t += $3 } END { printf "%.1f", t + 0 }' "$1"; }

h_valid=$(count_cat "$HEAD_STAT" Valid);     b_valid=$(count_cat "$BASE_STAT" Valid)
h_invalid=$(count_cat "$HEAD_STAT" Invalid); b_invalid=$(count_cat "$BASE_STAT" Invalid)
h_timeout=$(count_cat "$HEAD_STAT" Timeout); b_timeout=$(count_cat "$BASE_STAT" Timeout)
h_error=$(count_cat "$HEAD_STAT" Error);     b_error=$(count_cat "$BASE_STAT" Error)
h_mixed=$(count_cat "$HEAD_STAT" Mixed);     b_mixed=$(count_cat "$BASE_STAT" Mixed)
head_total=$(total_wall "$HEAD_STAT")
base_total=$(total_wall "$BASE_STAT")

regressions=()
soundness=()
improvements=()
errors=()

while read -r name hr hw br bw; do
  if [ "$br" = "Invalid" ] && [ "$hr" = "Valid" ]; then
    soundness+=("$name|$br|$hr")
  elif [ "$br" = "Valid" ] && [ "$hr" != "Valid" ] && [ "$hr" != "Timeout" ]; then
    regressions+=("$name|$br|$hr")
  elif [ "$br" = "Invalid" ] && [ "$hr" != "Invalid" ] && [ "$hr" != "Timeout" ]; then
    regressions+=("$name|$br|$hr")
  elif [ "$br" = "Timeout" ] && { [ "$hr" = "Valid" ] || [ "$hr" = "Invalid" ]; }; then
    improvements+=("$name|$br|$hr")
  fi

  # Any error from the PR's binary is a problem in its own right, whether or not
  # the base also errored on it — an error must never count as a pass.
  if [ "$hr" = "Error" ]; then
    errors+=("$name|$br|$hr|${head_shard[$name]:-}")
  fi
done < "$joined"

# ---- Overall verdict & exit code -------------------------------------------
# Errors fail the check independently of regressions/soundness; the headline
# shows the most severe issue but every applicable table is rendered below.
if [ "${#soundness[@]}" -gt 0 ]; then
  verdict=":x: **Soundness bug** — the PR reports a property Valid that the base found Invalid."
  exit_code=2
elif [ "${#regressions[@]}" -gt 0 ]; then
  verdict=":x: **Regression** — the PR changes ${#regressions[@]} result(s) for the worse."
  exit_code=1
elif [ "${#errors[@]}" -gt 0 ]; then
  verdict=":x: **Some error occurred during testing** — the PR's Kind 2 errored on ${#errors[@]} benchmark(s); see logs."
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
emit "| Result | PR head | Base |"
emit "|---|---:|---:|"
emit "| Valid | $h_valid | $b_valid |"
emit "| Invalid | $h_invalid | $b_invalid |"
emit "| Timeout | $h_timeout | $b_timeout |"
emit "| Error | $h_error | $b_error |"
if [ "$h_mixed" -gt 0 ] || [ "$b_mixed" -gt 0 ]; then
  emit "| Mixed | $h_mixed | $b_mixed |"
fi
emit "| **Total** | $n_head | $n_base |"
emit "| **Wall time** | ${head_total}s | ${base_total}s |"
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

# The Errors table has an extra column naming the shard job whose log holds each
# benchmark's Kind 2 output (dumped there under a "::group::" by run-benchmarks.sh).
emit_errors_table() {
  emit "### :boom: Errors (PR head)"
  emit "| Benchmark | Base | PR head | Output in job |"
  emit "|---|---|---|---|"
  local row name base head shard job
  for row in "$@"; do
    IFS='|' read -r name base head shard <<< "$row"
    if [ -n "$shard" ]; then job="\`benchmark (head $shard)\`"; else job="—"; fi
    emit "| \`$name\` | $base | $head | $job |"
  done
  emit ""
}

if [ "${#soundness[@]}" -gt 0 ]; then
  emit_table ":rotating_light: Soundness bugs" "${soundness[@]}"
fi
emit_table "Regressions" "${regressions[@]}"
if [ "${#errors[@]}" -gt 0 ]; then
  emit_errors_table "${errors[@]}"
fi
emit_table "Improvements (Timeout → solved)" "${improvements[@]}"

exit "$exit_code"
