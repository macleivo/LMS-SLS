#!/bin/bash
git clone https://github.com/Laakeri/maxpre
git clone https://github.com/arminbiere/cadical

cd maxpre
make lib

cd ../cadical
./configure
make
