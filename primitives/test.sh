make clean
make
cp libsat.a ./lib

gcc test.c -std=c99 -O2 -Wall -Iinclude -Llib -lsat -o test
