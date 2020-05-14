pragma solidity ^0.4.25;

contract addExp{

  function ae(uint x3, uint x2, uint x1, uint x0) returns (uint){
    uint x = x3+x2;
    uint y = x1+x0;
    return x**y;
  }

}
