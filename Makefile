# Makefile

.PHONY: help install clean

help:
	@echo "Available commands provided by Mitar's Makefile:"
	@echo "  make install    - "
	@echo "  make clean      - "

install:
	@rm -rf \
		$(HOME)/.Mitar/Lean2TeX \
		$(HOME)/.Mitar/css \
		$(HOME)/.Mitar/js
	@mkdir -p \
		$(HOME)/.Mitar/Lean2TeX \
		$(HOME)/.Mitar/css \
		$(HOME)/.Mitar/js
	@cp -rv Lean2TeX/. $(HOME)/.Mitar/Lean2TeX/
	@cp -rv css/. $(HOME)/.Mitar/css/
	@cp -rv js/. $(HOME)/.Mitar/js/
	@rm -rf $(HOME)/.Mitar/Lean2TeX/.lake
	@pip install -e .
	@echo "\n\033[1m\033[32m✓ Successfully Installed to \033[4m$(HOME)/.Mitar/\033[0m\n"

clean:
	@rm -rf build/ dist/
	@find . -name "Mitar.egg-info" -type d -exec rm -rf {} +
	@find . -name "__pycache__" -type d -exec rm -rf {} +
	@find . -name "*.pyc" -type f -delete