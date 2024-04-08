VERSION 0.6

ARG model

cmbc-image:
    FROM diffblue/cbmc:5.95.1


build:
    FROM +cmbc-image

    WORKDIR /workdir

    COPY src src
    RUN echo $model
    IF [$model == '']
        RUN cbmc src/main.c --unwind 50 --trace > output.txt 2>&1 || true
    ELSE
        RUN cbmc -D$model src/main.c --unwind 50 --trace > output.txt 2>&1 || true
    END
#--unwinding-assertions --cover assume 
    SAVE ARTIFACT output.txt AS LOCAL ./build/