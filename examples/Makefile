all: clear check

check:
	@echo "\n\e[31m***** REQUIRE FALSE *****\e[0m\n";
	@cd false && make -s check
	@echo "\n\e[31m*************************\e[0m\n";
	@echo "\n\e[32m***** REQUIRE TRUE ******\e[0m\n";
	@cd true && make -s check
	@echo "\n\e[32m*************************\e[0m\n";

cat:
	@echo "\n\e[31m***** REQUIRE FALSE *****\e[0m\n";
	@cd false && make -s cat
	@echo "\n\e[31m*************************\e[0m\n";
	@echo "\n\e[32m***** REQUIRE TRUE ******\e[0m\n";
	@cd true && make -s cat
	@echo "\n\e[32m*************************\e[0m\n";

compare:
	@echo "\n\e[31m***** REQUIRE FALSE *****\e[0m\n";
	@cd false && make -s compare
	@echo "\n\e[31m*************************\e[0m\n";
	@echo "\n\e[32m***** REQUIRE TRUE ******\e[0m\n";
	@cd true && make -s compare
	@echo "\n\e[32m*************************\e[0m\n";

clear:
	clear
