Dione Language Reference
========================


Types
-----

Primitive Types
***************

+ ``bool`` - Boolean type
+ ``int`` - Mathematical integer type
+ ``real`` - Mathematical real type
+ ``str`` - String
+ ``Enum[C1, C2, ...]`` - User defined enumeration type
+ ``IntEnum[lower:upper]`` - User defined numeric enumeration type.
  Can be compared with ``int`` values.

To be supported

+ ``char``
+ ``bytes``


Collection Types
****************

Currently, we only support ``T`` to be a primitive type.

+ ``Mapping[T1, T2]``- Mapping from ``T1`` type to ``T2`` type
+ ``NamedTuple[field1:T1, field2:T2, ...]`` - Tuple with named fields
+ ``Tuple[T1, T2, ...]`` - Tuple with anonymous fields
+ ``Sequence[T]`` -
+ ``Set[T]`` - Unordered set
+ ``Counter[T]`` - Multi-set



Language Syntax
---------------

Dione language is a strict subset of Python 3.7 by design.
We follow the `Abstract Grammar of Python 3.7`_ and describe the constraints over the abstract grammar for Dione.

.. _Abstract Grammar of Python 3.7: https://docs.python.org/3.7/library/ast.html#abstract-grammar

