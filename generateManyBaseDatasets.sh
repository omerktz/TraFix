#!/bin/bash
set -x
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_100 -po -c configs/codenatorN100.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_100 -po -c configs/codenatorN100.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_100 -po -c configs/codenatorN100.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_100 -po -c configs/codenatorN100.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_90 -po -c configs/codenatorN90.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_90 -po -c configs/codenatorN90.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_90 -po -c configs/codenatorN90.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_90 -po -c configs/codenatorN90.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_80 -po -c configs/codenatorN80.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_80 -po -c configs/codenatorN80.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_80 -po -c configs/codenatorN80.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_80 -po -c configs/codenatorN80.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_70 -po -c configs/codenatorN70.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_70 -po -c configs/codenatorN70.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_70 -po -c configs/codenatorN70.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_70 -po -c configs/codenatorN70.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_60 -po -c configs/codenatorN60.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_60 -po -c configs/codenatorN60.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_60 -po -c configs/codenatorN60.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_60 -po -c configs/codenatorN60.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_50 -po -c configs/codenatorN50.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_50 -po -c configs/codenatorN50.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_50 -po -c configs/codenatorN50.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_50 -po -c configs/codenatorN50.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_40 -po -c configs/codenatorN40.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_40 -po -c configs/codenatorN40.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_40 -po -c configs/codenatorN40.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_40 -po -c configs/codenatorN40.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_30 -po -c configs/codenatorN30.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_30 -po -c configs/codenatorN30.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_30 -po -c configs/codenatorN30.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_30 -po -c configs/codenatorN30.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_20 -po -c configs/codenatorN20.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_20 -po -c configs/codenatorN20.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_20 -po -c configs/codenatorN20.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_20 -po -c configs/codenatorN20.config &> /dev/null &
python codenator.py --vocabs -o timingResults/datasets/base_vocabs_10 -po -c configs/codenatorN10.config &> /dev/null &
python codenator.py -n 10000 -o timingResults/datasets/base_train_10 -po -c configs/codenatorN10.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_test_10 -po -c configs/codenatorN10.config &> /dev/null &
python codenator.py -n 1000 -o timingResults/datasets/base_validate_10 -po -c configs/codenatorN10.config &> /dev/null &
sleep 5
wait