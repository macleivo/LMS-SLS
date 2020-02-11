LMS-SLS: include/basis_pms.h include/pms.h src/*.cpp include/deci.h
	g++ -std=c++11 -Iinclude -Imaxpre/src -Icadical/src -Imaxpre src/*.cpp maxpre/src/lib/libmaxpre.a cadical/build/libcadical.a -static  -O3  -o LMS-SLS
