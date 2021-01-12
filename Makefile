.PHONY: all test clean parser check-dependencies test fmt

MILL = ./mill

WPTOOL_JAVA = wptool/src/wptool/Parser.java \
            wptool/src/wptool/Scanner.java

WPTOOL_JAR = out/wptool/jar/dest/out.jar
WPTOOL_LAUNCHER = ./out/wptool/launcher/dest/run
WPTOOL_SH  = ./wptool.sh

all: fmt parser $(WPTOOL_JAR) $(WPTOOL_SH)

parser: $(WPTOOL_JAVA)

clean:
	$(MILL) clean
	rm -f $(WPTOOL_JAVA)
	rm -f $(WPTOOL_SH)

check-dependencies:
	$(MILL) mill.scalalib.Dependency/updates

test: all
	$(MILL) wptool.test

$(WPTOOL_LAUNCHER): wptool/src/wptool/*.scala
	@echo $@
	$(MILL) wptool.launcher

$(WPTOOL_JAR): wptool/src/wptool/*.scala
	@echo $@
	$(MILL) wptool.jar

$(WPTOOL_SH): $(WPTOOL_LAUNCHER)
	@echo "[echo]  $@"; echo "#!/usr/bin/env bash" > $@; echo "export LD_LIBRARY_PATH=$(PWD)/wptool/lib" >> $@; echo "source $(WPTOOL_LAUNCHER)" >> $@
	@echo "[chmod] $@"; chmod +x $@

%.java: %.grammar
	java -jar beaver.jar -t $^

%.java: %.flex
	jflex -nobak $^

o: $(WPTOOL_OBJ)
	@echo $(WPTOOL_OBJ)

lib%.dylib: wptool/lib/lib%.dylib
	ln -s $<

fmt:
	$(MILL) mill.scalalib.scalafmt.ScalafmtModule/reformatAll __.sources
