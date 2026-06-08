import argparse
from .make import make

def Mitar_make(args: argparse.Namespace):
    make(args.input_file)

def main():

    parser = argparse.ArgumentParser(
        prog = "Mitar",
        description = "An automatic informalization tool for mathematical proofs in Lean4"
    )

    subparsers = parser.add_subparsers(
        title = "command",
        dest = "command",
        required = True
    )

    parser_hello = subparsers.add_parser("make", help="")
    parser_hello.add_argument("input_file", help="")
    parser_hello.set_defaults(func=Mitar_make)

    args = parser.parse_args()
    args.func(args)
