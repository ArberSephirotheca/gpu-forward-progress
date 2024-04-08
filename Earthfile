VERSION 0.8


cmbc-image:
    FROM diffblue/cbmc:5.95.1


build:
    FROM +cmbc-image

    WORKDIR /workdir

    COPY src src
    RUN cbmc src/main.c --unwind 50 --trace > output.txt 2>&1 || true
#--unwinding-assertions --cover assume 
    SAVE ARTIFACT output.txt AS LOCAL ./build/