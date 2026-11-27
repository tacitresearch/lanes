| Payments (`examples/payments/Shop.lean`) | A shop that charges each order through the payment model, retrying calls that time out under the order's key | Charged at most once per order in every run, under every environment and whatever the model allows, counting payments the service may have made without saying so (`Shop.charged_at_most_once`); model-checked on one order with crashes, where a retry without the key charges the order twice; that an order called paid has a payment that succeeded is checked, not proved |

- No adapter: the shop runs only in the checker and the proof.
