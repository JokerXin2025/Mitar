# Makefile

.PHONY: help install clean

help:
	@echo "Available commands provided by Mitar's Makefile:"
	@echo "  make install    - "
	@echo "  make clean      - "

# ProofScript 统一安装到用户根目录下与 `~/.Mitar/` 并列的 `~/.ProofScript/`。
# 源码位于 Mitar 的兄弟目录（`../ProofScript/`），所有项目共享这一份。
install:
	@rm -rf \
		$(HOME)/.ProofScript \
		$(HOME)/.Mitar/css \
		$(HOME)/.Mitar/js
	@mkdir -p \
		$(HOME)/.ProofScript \
		$(HOME)/.Mitar/css \
		$(HOME)/.Mitar/js
	@cp -rv ../ProofScript/. $(HOME)/.ProofScript/
	@cp -rv css/. $(HOME)/.Mitar/css/
	@cp -rv js/. $(HOME)/.Mitar/js/
	@rm -rf $(HOME)/.ProofScript/.lake $(HOME)/.ProofScript/.git $(HOME)/.ProofScript/.github $(HOME)/.ProofScript/.DS_Store
	@cd $(HOME)/.ProofScript && lake build
	@pip install -e .
	@echo "\n\033[1m\033[32m✓ Successfully Installed to \033[4m$(HOME)/.Mitar/\033[0m and \033[4m$(HOME)/.ProofScript/\033[0m\n"

clean:
	@rm -rf build/ dist/
	@find . -name "Mitar.egg-info" -type d -exec rm -rf {} +
	@find . -name "__pycache__" -type d -exec rm -rf {} +
	@find . -name "*.pyc" -type f -delete
