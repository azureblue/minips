CFLAGS = -O2 -Wall -Wextra
MINICELL = ../minicell
MINICELL_LIB = $(MINICELL)/build/libminicell.a

minips: minips.c $(MINICELL_LIB)
	$(CC) $(CFLAGS) -I$(MINICELL)/include -o $@ minips.c $(MINICELL_LIB)

$(MINICELL_LIB):
	$(MAKE) -C $(MINICELL) build/libminicell.a

clean:
	rm -f minips
