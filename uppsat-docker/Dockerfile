FROM anapsix/alpine-java
WORKDIR /home/root

COPY uppsat.jar /home/root/
COPY z3 /home/root/bin/
COPY example.smt2 /home/root/
COPY hard.smt2 /home/root/

RUN chmod +x /home/root/bin/z3
ENV PATH "$PATH:/home/root/bin"
ENV TIMEOUT="5"
ENV INPUT="example.smt2"
ENV APPROXIMATION="ijcar"

CMD env && timeout -t $TIMEOUT java -jar uppsat.jar -app=$APPROXIMATION $INPUT
