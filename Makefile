all: qrat-trim cheskol

qrat-trim: qrat-trim.c
	gcc qrat-trim.c -O2 -o qrat-trim

cheskol: cheskol.c
	gcc cheskol.c -O2 -o cheskol

clean:
	rm qrat-trim cheskol
