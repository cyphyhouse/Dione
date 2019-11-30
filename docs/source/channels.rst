==========================
ROS Communication Patterns
==========================

Topics, Services, and Actions can be considered as different channels with
varying reliability.

Documentation: https://wiki.ros.org/ROS/Patterns/Communication


------
Topics
------

Assumptions/Simplifications:

+ Simplify and merge both Publisher queue and Subscriber queue into a channel
  automaton with a certain size of queue.
+ Publish rate is determined by how often ``publish`` functions are called, and
  it can vary due to the control flow, block waiting, etc.
+ Subscriber spin rate is fairly fixed if user simply calls ``spin``. Even if
  user calls ``spinOnce``, we may still use the sleep rate in the main while loop.
+ Message latching is not considered.


---------
ActionLib
---------

Assumptions/Simplifications:

+ Consider only ``SimpleActionServer`` and ``SimpleActionClient``:
  only one goal is active and new goals preempt old goals.

  - Only the public member functions of ``SimpleActionServer`` are considered

+ a


Documentation:

+ https://wiki.ros.org/actionlib
+ https://wiki.ros.org/actionlib/DetailedDescription



===============================
Global Snapshot for Manufacture
===============================

Counter example on when making a decision on an incorrect global snapshot to convince people.