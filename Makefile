CFLAGS = -O2 -Wall -Wextra

minips: minips.c
	$(CC) $(CFLAGS) -o $@ minips.c

clean:
	rm -f minips
