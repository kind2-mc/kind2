#!/bin/bash

# Defaults.

master_update=false
dev_update=false
local_update=false
local_update_dir_default="../."
local_update_dir="$local_update_dir_default"
docker_push=false
docker_push_id_default="kind2-mc"
docker_push_id="$docker_push_id_default"

# Helpers.
function paint_green {
  printf "\033[32m$1\033[0m\n"
}
function paint_red {
  printf "\033[31m$1\033[0m\n"
}
function paint_bold {
  printf "\033[1m$1\033[0m\n"
}
function errcho {
  error=`paint_red "Error"`
  echo "${error}: $1" 1>&2
}
function error_exit {
  echo
  errcho "$1"
  echo
  exit 2
}
function print_help {
  echo "
/!\\ This script updates your `paint_bold LOCAL` images for the kind2 and
/!\\ kind2-dev docker container.
/!\\ It `paint_bold \"DOES NOT\"` update any remote repo or anything. To do
/!\\ that, use \`docker tag\` and \`docker push\` manually.

`paint_bold Usage`:
  `paint_bold -h`
    Prints this message.
  `paint_bold master`
    Updates the master image \`kind2\`.
  `paint_bold dev`
    Updates the dev image \`kind2-dev\`.
  `paint_bold \"local[=<DIR>]\"`
    Updates the local image from the sources in `paint_bold \"<DIR>/src\"`.
    If no directory is given, uses \`$local_update_dir_default\`.\
  `paint_bold \"push[=<DOCKER_ID>]\"`
    Runs
    > \`docker tag <image>:<tag> <DOCKER_ID>/<image>:latest\`
    and
    > \`docker push <DOCKER_ID>/<image>:latest\`
    for the master and/or dev image(s) created.
    If no docker identifier is given, uses \`$docker_push_id_default\`\
"
}
function print_help_err {
  print_help 1>&2
}
function unknown_arg {
  arg=`paint_red "$1"`
  print_help_err
  error_exit "unknown argument ${arg} $2"
}
function echo_run {
  echo
  echo "$1"
  $1
}

# CLAP.

while (( "$#" ))
do
  case "$1" in
    "-"*)
      # Iterate over characters.
      for (( i=0; i<${#1}; i++ )); do
        # Ignore first character, it's a dash.
        if [ "$i" -eq "0" ]
        then
          continue
        fi
        flag="${1:$i:1}"
        case "$flag" in
          "h")
            print_help
            exit 0 ;;
          *)
            unknown_arg "$flag" "in \``paint_red $1`\`"
        esac
      done
      shift
      ;;
    "master")
      master_update=true
      ;;
    "dev")
      dev_update=true
      ;;
    "local")
      local_update=true
      ;;
    "local="*)
      local_update=true
      local_update_dir=`echo "$1" | cut -d'=' -f 2`
      if [ ! -d "$local_update_dir" ]
      then
        error_exit \
          "local directory \``paint_red \"$local_update_dir\"`\` does not exist"
      fi
      ;;
    "push")
      docker_push=true
      ;;
    "push="*)
      docker_push=true
      docker_push_id=`echo "$1" | cut -d'=' -f 2`
      ;;
    *)
      unknown_arg "$1" ""
      ;;
  esac
  shift
done

# Check that docker is available.
docker -v 2>&1 > /dev/null
if [ "$?" -ne "0" ]
then
  echo "Command \`docker\` not found." 1>&2
  exit 2
fi

log_folder="./logs"
mkdir -p "$log_folder"

function update {
  name="$1"
  container="$2"
  should_docker_push="$3"
  echo
  printf "Updating `paint_bold \"$name\"` container `paint_bold \"$container\"` ... "
  log_file_out="$log_folder/$name.out"
  log_file_err="$log_folder/$name.err"
  docker build -t $container $name 1>"$log_file_out" 2>"$log_file_err"
  if [ "$?" -ne "0" ]
  then
    echo "`paint_red error`."
    error_exit "could not update `paint_bold $container` container from $name.
  see files `paint_bold $log_file_out` and `paint_bold $log_file_err`."
  else
    echo "`paint_green success`."
    # echo "(log files available in `paint_bold \"$log_folder/\"`)"
    # echo
    # Retrieve tag.
    tag=`\
      docker images $container \
      | sed -n 2p \
      | sed -e 's:[ ][ ]*: :g' \
      | cut -d ' ' -f 3\
    `
    if [ "$should_docker_push" = true ]
    then
      echo_run "docker images $container"
      echo_run "docker tag $container:$tag $docker_push_id/$container:latest"
      echo_run "docker push $docker_push_id/$container:latest"
    else
      echo "Tag: `paint_bold $tag`"
    fi
  fi
}

if [ "$master_update" = true ]
then
  update "master" "kind2" "$docker_push"
fi

if [ "$dev_update" = true ]
then
  update "dev" "kind2-dev" "$docker_push"
fi

if [ "$local_update" = true ]
then
  # Prepare stub.
  echo "copying"
  loc_kind_dir="local/kind2"
  mkdir -p "$loc_kind_dir"
  to_copy=`ls $local_update_dir | grep -v docker | sed -e "s:^:$local_update_dir/:" | tr "\n" " "`
  cp -rf $to_copy "$loc_kind_dir/."
  echo "done copying"
  # Change versioning, will fail because not in a git directory.
  cat "$loc_kind_dir/src/Makefile.in" \
  | sed -e 's:^GIT_DESCRIBE.*:GIT_DESCRIBE="local":g' \
  > "$loc_kind_dir/src/Makefile.in.tmp" \
  && mv "$loc_kind_dir/src/Makefile.in.tmp" "$loc_kind_dir/src/Makefile.in"
  make -C local/kind2 clean
  # exit 2
  update "local" "kind2-local" false
  rm -rf local/kind2
fi

echo
