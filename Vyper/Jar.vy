#pragma version >0.3.0

bal: public(HashMap[address, uint256])

@external
@payable
def deposit():
    self.bal[msg.sender] += msg.value

@external
@nonreentrant("withdrawlock")
def withdraw():
    assert bal[msg.sender] != 0
    send(msg.sender, bal[msg.sender])
    self.bal[msg.sender] = 0