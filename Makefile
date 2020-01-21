all: solve

solve: solve.c
	${CC} -O3 -g -ggdb -Wall -Wpedantic -Werror=vla -o solve solve.c nauty.a -mpopcnt

clean:
	rm -f solve
