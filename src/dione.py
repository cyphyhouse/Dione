""" Entry point for using Input/Output automaton frontend"""

import argparse
import asyncio
import sys

from src.frontend.translator_dafny import TranslatorDafny
from src.verification_engine.prover_dafny import ProverDafny


async def prove(dfy_exe, dfy_code):
    async with ProverDafny(dfy_exe) as prover:  # This creates a new process
        print(await prover.verify(dfy_code))


def main(args=None):
    if args is None:
        # main function shouldn't take arguments if using setuptools.
        # Hence, we read arguments from sys.argv
        args = sys.argv[1:]

    config = parse_args(args)

    dfy_exe = "C:\\Users\\chsieh16\\Documents\\dafny\\Binaries\\DafnyServer.exe"
    dfy_code = TranslatorDafny(config.ioa_file).get_dafny_code()

    if sys.platform == 'win32':
        asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())

    asyncio.run(prove(dfy_exe, dfy_code))


def parse_args(args):
    parser = argparse.ArgumentParser(description='Verification/Simulation for Input/Output Automaton')
    parser.add_argument('ioa_file', type=argparse.FileType('r'), help='Input IOA file')
    return parser.parse_args(args)


if __name__ == "__main__":
    main()
