/**
 * A piece of marked ground. 
 */
public class MarkedGround extends Ground
{

  MarkedGround (Position p) {
    super (p);
  }

  /** @informal: this kind of crate is marked */
  public boolean isMarked () {
    return true;
  }

  public String toString () {
    return "groundX(" + position.x + "," + position.y + ")";
  }
}
