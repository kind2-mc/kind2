#!/bin/bash

# A job script for qsub to be used within an array job
#
# Author: Christoph Sticksel (christoph-sticksel@uiowa.edu)

PATH=$SGE_O_PATH

# Get the file to process by this task
JOBFILE=$1
shift 

# Get the time limit for this task
CPULIMIT=$(( $1 * 4 ))
WCLIMIT=$1
shift

# Read the n-th line from the file listing the jobs 
JOB=$(sed -n -e "$SGE_TASK_ID p" $JOBFILE)

# Get the last element in a list and take its base name
for JOB_NAME in $JOB; do true; done
JOB_BASENAME=$(basename $JOB_NAME)

# Set the shell that should be used to run the job.
#$ -S /bin/bash

# Make sure that the .e and .o file arrive in the working
# directory. Set the current working directory as the location for the
# error and output files.  (Will show up as .e and .o files) 

# Merge stdout and stderr and output to /localscratch, copy to the
# final directory at the end 
#$ -j y

uptime >> $SGE_STDOUT_PATH

# Copy file to /localscratch
cp $JOB $TMPDIR

# Run the command on the file
# exec 3>&1 4>&2
# TIMEFORMAT='%3R %3U %3S' EXEC_TIME=$( { time $* /localscratch/$JOB_BASENAME 1>&3 2>&4; } 2>&1 ) 
# exec 3>&- 4>&-

~/bin/TreeLimitedRun $CPULIMIT $WCLIMIT $* $TMPDIR/$JOB_BASENAME 2>&1

# TIMEFORMAT=$'\nreal\t%3R\nuser\t%3U\nsys%3S' time $* $JOB  

# Remove file
rm /$TMPDIR/$JOB_BASENAME

# Move the output to the final directory 
mv $SGE_STDOUT_PATH $JOB_BASENAME
echo $EXEC_TIME >> $JOB_BASENAME

