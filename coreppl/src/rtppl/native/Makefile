all: validate pprint

validate: validate.mc rtppl.mc
	mi compile $<

pprint: pprint.mc rtppl.mc
	mi compile $<

rtppl.mc: rtppl.syn lexer.mc
	mi syn $< $@

clean:
	rm -f rtppl.mc pprint validate
