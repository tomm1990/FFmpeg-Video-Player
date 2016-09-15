all: project

project: main.o
	gcc main.o -o video -lavutil -lavformat -lavcodec -lswscale -lz -lm `sdl-config --cflags --libs`

main.o: main.c
	gcc -c -std=gnu99 main.c -lavutil -lavformat -lavcodec -lswscale -lz -lm `sdl-config --cflags --libs`

clean:
	find . ! -name '*.c' ! -name '*.mpg' ! -name makefile ! -name '*.txt' -type f -delete
	find . ! -name DB -mindepth 1 -type d -exec rm -rf {} \;
