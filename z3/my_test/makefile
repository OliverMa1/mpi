CC = g++
CFLAGS =-I. -std=c++11 -I ../src/api/c++ -I ../src/api/ -L ../build/ -lz3
DEPS = teacher.h
OBJ = main.o
ODIR=.
%.o: %.cpp $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)
main: $(OBJ)
	$(CC) -o $@ $^ $(CFLAGS)

.PHONY: clean

clean:
	rm -f $(ODIR)/*.o *~ core $(INCDIR)/*~ 
