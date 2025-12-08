all: clear check

check:
	@echo "\n***** REQUIRE FALSE *****\n";
	@cd false && make -s check
	@echo "\n*************************\n";
	@echo "\n***** REQUIRE TRUE ******\n";
	@cd true && make -s check
	@echo "\n*************************\n";

cat:
	@echo "\n***** REQUIRE FALSE *****\n";
	@cd false && make -s cat
	@echo "\n*************************\n";
	@echo "\n***** REQUIRE TRUE ******\n";
	@cd true && make -s cat
	@echo "\n*************************\n";

compare:
	@echo "\n***** REQUIRE FALSE *****\n";
	@cd false && make -s compare
	@echo "\n*************************\n";
	@echo "\n***** REQUIRE TRUE ******\n";
	@cd true && make -s compare
	@echo "\n*************************\n";

clear:
	clear
