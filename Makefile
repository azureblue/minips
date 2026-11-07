CFLAGS = -O2 -Wall -Wextra

minips: minips.c read_buffer.c read_buffer.h
	$(CC) $(CFLAGS) -o $@ minips.c read_buffer.c

clean:
	rm -f minips
