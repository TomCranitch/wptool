.PHONY: all test clean parser check-dependencies test

MILL = ./mill

WEMELT_JAVA = wptool/src/wptool/Parser.java \
            wptool/src/wptool/Scanner.java

WEMELT_JAR = out/wptool/jar/dest/out.jar
WEMELT_LAUNCHER = ./out/wptool/launcher/dest/run
WEMELT_SH  = ./wptool.sh

all: parser $(WEMELT_JAR) $(WEMELT_SH)

parser: $(WEMELT_JAVA)

clean:
	$(MILL) clean
	rm -f $(WEMELT_JAVA)
	rm -f $(WEMELT_SH)

check-dependencies:
	$(MILL) mill.scalalib.Dependency/updates

test: all
	$(MILL) wptool.test

$(WEMELT_LAUNCHER): wptool/src/wptool/*.scala
	@echo $@
	$(MILL) wptool.launcher

$(WEMELT_JAR): wptool/src/wptool/*.scala
	@echo $@
	$(MILL) wptool.jar

$(WEMELT_SH): $(WEMELT_LAUNCHER)
	@echo "[echo]  $@"; echo "#!/usr/bin/env bash" > $@; echo "export LD_LIBRARY_PATH=$(PWD)/wptool/lib" >> $@; echo "source $(WEMELT_LAUNCHER)" >> $@
	@echo "[chmod] $@"; chmod +x $@

%.java: %.grammar
	java -jar beaver.jar -t $^

%.java: %.flex
	jflex -nobak $^

o: $(WEMELT_OBJ)
	@echo $(WEMELT_OBJ)

lib%.dylib: wptool/lib/lib%.dylib
	ln -s $<
