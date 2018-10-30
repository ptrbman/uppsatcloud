FROM java:7
WORKDIR /home/root

COPY uppsat.jar /home/root/
COPY example.smt2 /home/root/

RUN mkdir /home/root/bin
RUN wget http://user.it.uu.se/~petba168/z3-4.5.0 -O /home/root/bin/z3
RUN chmod +x /home/root/bin/z3
ENV PATH "$PATH:/home/root/bin"

ENTRYPOINT ["java", "-jar", "uppsat.jar"]