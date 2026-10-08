#!/usr/bin/env python3
"""Pinned exact scalar comparisons with prepared operands and protocol controls.

Operations include a result guard and temporary cleanup. FLINT rounding uses
its floor/ceil APIs. Z3 RCF has no matching rounding API in this adapter, so
those comparisons are deliberately unavailable. Setup is never timed.
"""
from __future__ import annotations
import argparse
import ctypes
from fractions import Fraction
from importlib.metadata import version
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))


def validate(operation, size):
    if operation not in ('add','sqrt','compare','floor','ceil','rational'):
        raise ValueError('unknown operation')
    allowed=(2,4,8) if operation in ('add','sqrt') else ((16,64,256,1024) if operation=='rational' else (4,16,64,256))
    if type(size) is not int or size not in allowed:
        raise ValueError('unsupported size')


class Flint:
    def __init__(self, operation,size):
        from scripts.oracle.real_algebraic_qqbar import QQBar
        validate(operation,size)
        self.operation,self.size=operation,size
        self.oracle=QQBar();o=self.oracle
        self.one=o.number(1);self.two=o.number(2)
        if operation=='rational':
            self.rational=Fraction((2**size-1)//3,2**size+1)
            self.expected=o.number(self.rational)
        elif operation in ('add','sqrt'):
            self.a=o.to_real(o.nth_root(self.two,size))

        else:
            self.a=o.unary('sqrt',self.two)
            shift=o.number(Fraction(1,2**size))
            self.b=o.binary('add',self.a,shift)
            self.near=o.binary('add',self.one,o.binary('mul',self.a,shift))
            self.expected=self.one if operation=='floor' else self.two
        self.retained=len(o.owned)

    def run(self):
        o=self.oracle;checkpoint=len(o.owned)
        try:
            op=self.operation
            if op=='compare':
                return o.compare(self.a,self.b)<0
            if op=='rational':result=o.number(self.rational)
            elif op=='add':result=o.binary('add',self.a,self.one)
            elif op=='sqrt':result=o.unary('sqrt',self.a)
            else:result=o.unary(op,self.near)
            if op=='sqrt':
                return o.compare(o.binary('mul',result,result),self.a)==0 and o.compare(result,self.one)>0
            if op=='add':
                value=o.binary('sub',result,self.one)
                for _ in range(self.size.bit_length()-1):value=o.binary('mul',value,value)
                return o.compare(value,self.two)==0 and o.compare(result,self.one)>0
            return o.compare(result,self.expected)==0
        finally:
            for value,ctx in reversed(o.owned[checkpoint:]):
                o.lib.gr_heap_clear(value,ctypes.byref(ctx))
            del o.owned[checkpoint:]

    def close(self):self.oracle.close()


class Z3:
    def __init__(self,operation,size):
        import z3
        from z3 import z3rcf
        validate(operation,size)
        if operation in ('floor','ceil'):
            raise ValueError('no matching Z3 RCF floor/ceil API')
        if version('z3-solver')!='4.15.4.0' or z3.get_version()!=(4,15,4,0):
            raise RuntimeError('requires z3-solver 4.15.4.0')
        self.operation,self.size=operation,size
        self.context=z3.Context();self.api=z3rcf
        self.one,self.two,self.zero=map(self.num,(1,2,0))
        if operation=='rational':
            q=Fraction((2**size-1)//3,2**size+1)
            self.rational=f'{q.numerator}/{q.denominator}'
            self.expected=self.num(self.rational)
        elif operation in ('add','sqrt'):
            self.a=sorted(z3rcf.MkRoots([-self.two]+[self.zero]*(size-1)+[self.one],self.context))[-1]

        else:
            self.a=sorted(z3rcf.MkRoots([-self.two,self.zero,self.one],self.context))[-1]
            self.b=self.a+self.num(f'1/{2**size}')

    def num(self, x):
        return self.api.RCFNum(x,self.context)

    def run(self):
        op=self.operation
        if op=='compare':return self.a<self.b
        if op=='rational':result=self.num(self.rational)
        elif op=='add':result=self.a+self.one
        else:result=sorted(self.api.MkRoots([-self.a,self.zero,self.one],self.context))[-1]
        if op=='sqrt':return result*result==self.a and result>self.one
        if op=='add':
            value=result-self.one
            for _ in range(self.size.bit_length()-1):value=value*value
            return value==self.two and result>self.one
        return result==self.expected

    def close(self):pass


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tool',choices=('flint','z3'),required=True)
    args=parser.parse_args();endpoints={}
    try:
        for line in sys.stdin:
            try:
                req=json.loads(line);op,size=req['operation'],req['size']
                validate(op,size)
                control=req.get('control',False)
                if type(control) is not bool:raise ValueError('control must be Boolean')
                key=op,size
                if key not in endpoints:
                    endpoints[key]=(Flint if args.tool=='flint' else Z3)(op,size)
                result=True if control else endpoints[key].run()
                if not result:raise ArithmeticError('exact result guard failed')
                reply=dict(ok=True,result=result)
            except (KeyError,ValueError,ArithmeticError,TypeError) as error:
                reply=dict(ok=False,error=str(error))
            print(json.dumps(reply),flush=True)
    finally:
        for endpoint in endpoints.values():endpoint.close()


if __name__=='__main__':main()
