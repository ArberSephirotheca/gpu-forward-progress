VERSION 0.8


cmbc-image:
    FROM diffblue/cbmc:5.95.1


build:
    FROM +cmbc-image

    WORKDIR /workdir

    COPY src src
    RUN cbmc src/main.c -unwind 10 --trace --unwinding-assertions > output.txt 2>&1 || true

    SAVE ARTIFACT output.txt AS LOCAL ./build/