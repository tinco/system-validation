/**
 * A piece of marked ground. 
 */
public class MarkedGround extends Ground
{

  MarkedGround (Position p) {
    super (p);
  }

  /** @informal: this kind of crate is marked */
  //@ also ensures \result == true; 
  public boolean isMarked () {
    return true;
  }

  public String toString () {
    return "groundX(" + position.x + "," + position.y + ")";
  }
}
