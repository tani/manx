CFLAGS=-O3 -march=native -mfpmath=sse -fexcess-precision=fast -ffast-math -funroll-loops -flto -fopenmp

all: manx

manx: manx.pl
	gplc -C '${CFLAGS}' $<
