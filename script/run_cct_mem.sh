#! /bin/bash

# set -euo pipefail

CUR_DIR=$(pwd)
BUILD_PATH=${CUR_DIR}/../build
RUN_DIRECTORY_64=${BUILD_PATH}/bin64
RUN_DIRECTORY_32=${BUILD_PATH}/bin32
RUN_DIRECTORY=${RUN_DIRECTORY_32}
if [ ! -d ${RUN_DIRECTORY_64} ]; then
    RUN_DIRECTORY=${RUN_DIRECTORY_32}
else
    RUN_DIRECTORY=${RUN_DIRECTORY_64}
fi

APP_FULL_PATH=$1
APP_ARG1=$2
APP_ARG2=$3
APP_ARG3=$4
APP_ARG4=$5
APP_ARG5=$6
APP_ARG6=$7
APP_ARG7=$8
APP_ARG8=$9

echo "${RUN_DIRECTORY}/drrun -t drcctlib_memory_only -- ${APP_FULL_PATH} $APP_ARG1 $APP_ARG2 $APP_ARG3 $APP_ARG4 $APP_ARG5 $APP_ARG6 $APP_ARG7 $APP_ARG8"
${RUN_DIRECTORY}/drrun -t drcctlib_memory_only -- ${APP_FULL_PATH} $APP_ARG1 $APP_ARG2 $APP_ARG3 $APP_ARG4 $APP_ARG5 $APP_ARG6 $APP_ARG7 $APP_ARG8
