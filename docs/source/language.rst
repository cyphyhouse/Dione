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



