FROM gcc:13-bookworm
WORKDIR /app
COPY pink_2.c pink_ludo.html cute.css ./
RUN gcc -O2 -pthread pink_2.c -o pink_ludo
EXPOSE 8080
CMD ["./pink_ludo"]