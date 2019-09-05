""" Python wrapper for calling Dafny proof assistant """

import asyncio
import base64
import json
import re

from dione.verification_engine.prover_interface import ProverInterface


class ProverDafny(ProverInterface):
    def __init__(self, dafny_server_exe):
        super(ProverDafny, self).__init__()
        self.__dfy_exe = dafny_server_exe
        self.proc = None

    async def __aenter__(self):
        self.proc = await asyncio.create_subprocess_exec(
            self.__dfy_exe,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            text=True
        )
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        out, err = await self.proc.communicate(b"quit")
        print(self.__parse_output(out))

    @staticmethod
    def __parse_output(msg_stream) -> bool:
        msgs = msg_stream.split(b'\n')
        # print(msgs[0])  # == b'Verification completed successfully!'
        return msgs  # [1] == b'[SUCCESS] [[DAFNY-SERVER: EOM]]'

    async def __run_task(self, command, code, args=None) -> str:
        if args is None:
            args = []
        command = command.encode('ascii') + b'\n'
        task = json.dumps({
            'args': args,
            'filename': '<none>',
            'source': code,
            'sourceIsFile': False}).encode('ascii')
        b64task = base64.b64encode(task)  # task has to be in base64

        self.proc.stdin.write(command)
        self.proc.stdin.write(b64task)
        self.proc.stdin.write_eof()
        await self.proc.stdin.drain()

        ret = b''
        line = b''
        pattern = br'\[(SUCCESS|FAILURE)\] \[\[DAFNY-SERVER: EOM\]\]'
        while not self.proc.stdout.at_eof() and \
                not re.match(pattern, line):
            ret += line
            line = await self.proc.stdout.readline()

        return ret.decode('ascii')

    async def verify(self, code, args=None):
        return await self.__run_task('verify', code, args)

    async def counter_example(self, code, args=None):
        return await self.__run_task('counterExample', code, args)
