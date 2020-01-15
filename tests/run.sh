#!/bin/bash

# Prints usage.
function print_usage {
  cat <<EOF
Usage: `basename $0` <DIR> <CMD>
with
  * <DIR> the test directory
  * <CMD> the Kind 2 command to test
(Passing "-h" or "--help" as argument prints this message.)

Tests Kind 2 on the lustre files in a directory. The directory should be
structured as follows. Directory
  * "success"     contains the files with only valid properties
  * "falsifiable" contains the files with at least one falsifiable property
  * "error"       contains the files on which Kind 2 fails with error code 2.
EOF
}

# Print usage if asked.
for arg in "$@"; do
  if [[ "$arg" = "-h" || "$arg" = "--help" ]]; then
    print_usage
    exit 0
  fi
done

test_dir=`echo "$1" | sed 's:/$::'`

# Make sure folder exists.
if [ ! -d "$test_dir" ]; then
  print_error "directory \"$test_dir\" does not exist"
fi

contract_dir="${test_dir}/contracts"

shift
k2_args="$@"

basic_k2_cmd="$k2_args --color false --check_subproperties true"
contract_k2_cmd="$basic_k2_cmd --modular true --compositional true"

success_code="20"
falsifiable_code="10"
timeout_code="0"
error_code="2"

success_dir="success"
falsifiable_dir="falsifiable"
error_dir="error"

tests_ok="true"

# Prints an error taking the lines as argument.
# Exit with exit code 2.
function print_error {
  print_usage
  echo
  echo -e "\033[31mError\033[0m:"
  for line in "$@"; do
    echo "  $line"
  done
  echo
  exit 2
}


# Returns the log file corresponding to a file.
# Simply appends ".log" at the end of the path.
function log_file_of {
  file="$1"
  echo "$1.log"
}

# Returns a string version of an exit code.
function str_of_code {
  if [ "$1" -eq "$success_code" ] ; then
    echo "success ($success_code)"
  elif [ "$1" -eq "$falsifiable_code" ]; then
    echo "falsifiable ($falsifiable_code)"
  elif [ "$1" -eq "$timeout_code" ]; then
    echo "timeout ($timeout_code)"
  else
    echo "error ($1)"
  fi
}

function name_of_path {
  echo $1 | sed -e 's:.*/::g'
}

# Runs a test on a file, takes the file path, the expected exit code and the
# Kind 2 command as arguments.
function run_one {
  file_path="$1"
  shift
  expected_code="$1"
  shift
  full_kind2_cmd="$@ $file_path"
  expected_code_str=`str_of_code "$expected_code"`

  printf "|   %-40s ... " "`name_of_path $file_path`"
  log_file_path=`log_file_of "$file_path"`
  $full_kind2_cmd &> $log_file_path
  exit_code="$?"
  if [ "$exit_code" -ne "$expected_code" ]; then
    tests_ok="false"
    exit_code_str=`str_of_code "$exit_code"`
    echo -e "\033[31merror\033[0m"
    echo -e "\033[31m!\033[0m      expected $expected_code_str"
    echo -e "\033[31m!\033[0m      but got  $exit_code_str"
    echo -e "\033[31m!\033[0m      See log in \"$log_file_path\"."
  else
    echo -e "\033[32mok\033[0m"
    rm $log_file_path
  fi
}

# Constructs the find command from a directory and a subdirectory.
function find_tests {
  echo "find ${1}/${2} -iname '*.lus'"
}

# Runs the tests in some directory, takes the working directory and the Kind 2
# command as arguments.
function run_in {
  work_dir="$1"
  shift
  kind2_cmd="$@"
  # Falsifiable
  find_cmd=`find_tests $work_dir $falsifiable_dir`
  file_count=`eval $find_cmd | wc -l | tr -d ' '`
  echo "| Running \"falsifiable\" ($file_count files)"
  for file in `eval $find_cmd`; do
    run_one "$file" "$falsifiable_code" "$kind2_cmd"
  done

  # Success
  find_cmd=`find_tests "$work_dir" "$success_dir"`
  file_count=`eval $find_cmd | wc -l | tr -d ' '`
  echo "| Running \"success\" ($file_count files)"
  for file in `eval $find_cmd`; do
    run_one "$file" "$success_code" "$kind2_cmd"
  done

  # Error
  find_cmd=`find_tests $work_dir $error_dir`
  file_count=`eval $find_cmd | wc -l | tr -d ' '`
  echo "| Running \"error\" ($file_count files)"
  for file in `eval $find_cmd`; do
    run_one "$file" "$error_code" "$kind2_cmd --lus_strict true"
  done
}

# Runs the tests on normal and contract.
function run_all {

  echo
  echo "|===| Running normal tests."
  echo -e "| > \033[1m$basic_k2_cmd\033[0m"
  echo "|"
  run_in "$test_dir" "$basic_k2_cmd"
  echo "|===| Done."
  echo

  # echo "|===| Running contract tests."
  # echo -e "| > \033[1m$contract_k2_cmd\033[0m"
  # echo "|"
  # run_in "$contract_dir" "$contract_k2_cmd"
  # echo "|===| Done."
  # echo
}




# Running tests.
run_all

# Shouting if there was an error.
if [ "$tests_ok" = "false" ]; then
  echo -e "\033[31mError\033[0m: some test failed."
  echo ""
  exit 2
else
  exit 0
fi
