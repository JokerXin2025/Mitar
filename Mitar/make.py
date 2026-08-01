import sys, json, subprocess
from pathlib import Path
from Mitar.Rules import Initialize
from Mitar.engine import ProofEngine

def make(input_path: str):

    Initialize()
    input_file = Path(input_path)
    json_file = input_file.with_name(f"{input_file.stem}_Lean2TeX.json")
    output_file = input_file.with_suffix(".html")

    if not input_file.exists():
        # Error: Input file not found
        print(f"\n\033[31m\033[1m✗ File \033[4m{input_file}\033[0m\033[31m\033[1m not found\033[0m\n")
        return

    if json_file.exists():
        json_file.unlink()

    print(f"Building Lean project to extract proof steps...")
    result = subprocess.run(
        ["lake", "build"],
        cwd = Path.cwd(),
        text = True,
        capture_output = True
    )

    if result.returncode:
        # Error: Lean4 build failure
        print(f"\n\033[31m\033[1m✗ Lean2TeX failed on building \033[4m{input_file}\033[0m\n")
        return

    if json_file.exists():
        with open(json_file, 'r', encoding = 'utf-8') as f:
            data = json.load(f)
    else:
        # Error: Lean2TeX internal error
        print(f"\n\033[31m\033[1m✗ Some internal error from Lean2TeX occurred\033[0m\n")
        return

    output_file.write_text(ProofEngine(data).make(), encoding = "utf-8")
    print(f"\n\033[32m\033[1m✓ Output file has been saved to \033[4m{output_file}\033[0m\n")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python make.py <input_file.lean>")
    else:
        make(sys.argv[1])
