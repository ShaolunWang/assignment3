fixes:
	rg -n FIXME
todo:
	rg -n TODO
compile:
	./compile.sh
run:
	./run.sh examples/turtleAndRabbit.rab turtleAndRabbit.gif
test:
	./test.sh test.rab
all: 
	make compile && make test
