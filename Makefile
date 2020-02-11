LMS-SLS: include/basis_pms.h include/pms.h src/*.cpp include/deci.h
	g++ -std=c++11 -Iinclude -Icadical/src -Imaxpre src/*.cpp maxpre/libmaxpre.a cadical/build/libcadical.a -static  -O3  -o LMS-SLS
