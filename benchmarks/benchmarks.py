from schemas import types

class Benchmark:
    def __init__(self, name, config, benches):
        self.name = name
        self.config = config
        self.benches = benches

class TestCase:
    def __init__(self, name, description, landmarks, input_args, output, solutions, max_length=12):
        self.name = name
        self.description = description
        self.landmarks = landmarks
        self.input = input_args
        self.output = output
        self.solutions = solutions
        self.max_length = max_length

slack_bench = Benchmark("slack", "configs/slack_config.json",
[
    TestCase(
        "1.1",
        "Retrieve all member emails from channel name",
        [],
        {
            "channel_name": types.PrimString("objs_conversation.name")
        },
        [types.ArrayType(None, types.PrimString("objs_user_profile.email"))],
        [[
            "\\channel_name -> {",
            "let x0 = /conversations.list_GET()",
            "x1 <- x0.channels",
            "if x1.name = channel_name",
            "let x2 = /conversations.members_GET(channel=x1.id)",
            "x3 <- x2.members",
            "let x4 = /users.profile.get_GET(user=x3)",
            "return x4.profile.email",
            "}"
        ]],
        20
    ),
    TestCase(
        "1.2",
        "Send a message to some user given the email address",
        [],
        {
            "email": types.PrimString("objs_user_profile.email")
        },
        [types.SchemaObject("objs_message")],
        [[
            "\\email -> {",
            "let x0 = /users.lookupByEmail_GET(email=email)",
            "let x1 = /conversations.open_POST(users=x0.user.id)",
            "let x2 = /chat.postMessage_POST(channel=x1.channel.id)",
            "return x2.message",
            "}"
        ]],
        10
    ),
    TestCase(
        "1.3",
        "Get all unread message for a user",
        [],
        {
            "user_id": types.PrimString("defs_user_id")
        },
        [types.ArrayType(None, types.PrimString("objs_message"))],
        [[
            "\\user_id -> {",
            "let x0 = /users.conversations_GET(user=user_id)",
            "x1 <- x0.channels",
            "let x2 = /conversations.info_GET(channel=x1.id)",
            "let x3 = x2.last_read",
            "let x5 = /conversations.history_GET(channel=x2.id, oldest=x3)",
            "return x5",
            "}"
        ]],
        10
    )
])

stripe_bench = Benchmark("stripe", "configs/stripe_config.json",
[
     TestCase(
         "2.1",
         "Make a subscription to a product for a customer",
         [],
         {
             "customer_id": types.PrimString("customer.id"),
             "product_id": types.PrimString("product.id")
         },
         [types.SchemaObject("subscription")],
         [[
             "\\customer_id product_id => {",
             "let x1 = /v1/prices_GET(product=product_id);",
             "x2 <- x1.data",
             "let x3 = /v1/subscriptions_POST(customer=customer_id, items[0].price=x2.id)",
             "return x3",
             "}"
         ]]
     ),
     TestCase(
         "2.2",
         "Charge a saved card given customer id",
         [],
         {
             "customer_id": types.PrimString("customer.id"),
             "cut": types.PrimString("fee.currency"),
             "amt": types.PrimInt("price.unit_amount")
         },
         [types.SchemaObject("payment_intent")],
         [[
             "\\customer_id cur amt => {",
             "let x1 = /v1/payment_methods_GET(customer=customer_id, type=card)",
             "let x2 = /v1/payment_intents_POST(customer=customer_id, payment_method=x1.id, currency=cur, amount=amt)",
             "let x3 = /v1/payment_intents/{pi}/confirm_POST(pi=x2.id, setup_future_usage=off_session)",
             "return x3",
             "}"
         ]]
     ),
     TestCase(
         "2.3",
         "Subscribe to multiple items",
         [],
         {
             "customer_id": types.PrimString("customer.id"),
             "product_ids": types.ArrayType(None, types.PrimString("product.id"))
         },
         [types.ArrayType(None, types.SchemaObject("subscription"))],
         [[
             "\\customer_id product_ids => {",
             "x0 <- product_ids",
             "let x1 = /v1/prices_GET(product=x0)",
             "let x2 = x1.data.map((x3) => {",
             "let x4 = /v1/subscriptions_POST(customer=customer_id, items[0].price=x3.id)",
             "return x4",
             "})",
             "return x2",
             "}",
             "return x0",
             "}"
         ]]
     ),
     TestCase(
         "2.4",
         "Create a product and invoice a customer",
         [],
         {
             "product_name": types.PrimString("product.name"),
             "customer_id": types.PrimString("customer.id"),
             "currency": types.PrimString("fee.currency"),
             "unit_amount": types.PrimInt("price.unit_amount")
         },
         [types.SchemaObject("invoiceitem")],
         [[
             "\\product_name customer_id currency unit_amount -> {",
             "let x0 = /v1/products_POST(name=product_name)",
             "let x1 = /v1/prices_POST(currency=currency, product=x0.id, unit_amount=unit_amount)",
             "let x2 = /v1/invoiceitems_POST(customer=customer_id, price=x1.id)",
             "return x2",
             "}"
         ]]
     ),
     TestCase(
         "2.5",
         "sending invoice",
         [],
         {
             "customer_id": types.PrimString("customer.id"),
             "price_id": types.PrimString("plan.id")
         },
         [types.SchemaObject("invoice")],
         [[
             "\\customer_id price_id => {",
             "let x1 = /v1/invoiceitems_POST(customer=customer_id, price=price_id);",
             "let x2 = /v1/invoices_POST(customer=x1.customer);",
             "let x3 = /v1/invoices/{invoice}/send_POST(invoice=x2.id);",
             "return x3;",
             "}"
         ]]
     ),
     TestCase(
         "2.6",
         "Retrieve customer by email",
         [],
         {
             "customer_email": types.PrimString("customer.email")
         },
         [types.SchemaObject("customer")],
         [[
             "\\customer_email -> {",
             "let x0 = /v1/customers_GET()",
             "x1 <- x0.data",
             "if x1.email = customer_email",
             "return x1",
             "}"
         ]]
     ),
    TestCase(
        "2.7",
        "Get a list of receipts for a customer",
        [],
        {
            "customer_id": types.PrimString("customer.id")
        },
        [types.ArrayType(None, types.SchemaObject("charge"))],
        [[
            "\\customer_id -> {",
            "let x1 = /v1/invoices_GET(customer=customer_id)",
            "x2 <- x1.data",
            "let x3 = /v1/charges/{charge}_GET(charge=x2.charge)",
            "return x3",
            "}"
        ]]
    ),
    TestCase(
        "2.8",
        "Get refund for given subscription",
        [],
        {
            "subscription_id": types.PrimString("subscription.id")
        },
        [types.SchemaObject("refund")],
        [[
            "\\subscription_id -> {",
            "let x0 = /v1/subscriptions/{subscription_exposed_id}_GET(subscription_exposed_id=subscription_id)",
            "let x1 = /v1/invoices_GET(customer=x0.customer)",
            "x2 <- x1.data",
            "let x3 = /v1/refunds/{refund}_POST(refund=x2.charge)",
            "return x3",
            "}"
        ]]
    ),
    TestCase(
        "2.9",
        "Get email of all customers",
        [],
        {
        },
        [types.ArrayType(None, types.PrimString("customer.email"))],
        [[
            "\\ -> {",
            "let x0 = /v1/customers_GET()",
            "x1 <- x0.data",
            "return x1.email",
            "}"
        ]]
    ),
    TestCase(
        "2.10",
        "Get email of subscribers to some product",
        [],
        {
            "product_id": types.PrimString("product.id")
        },
        [types.ArrayType(None, types.PrimString("customer.email"))],
        [[
            "\\product_id => {",
            "let x1 = /v1/subscriptions_GET()",
            "x2 <- x1",
            "if x2.items.product = product_id",
            "let x3 = /v1/customers/{customer}_GET(customer=x2.customer_id)",
            "return x3",
            "}"
        ]]
    ),
    TestCase(
        "2.11",
        "Get last 4 digit of card for a customer",
        [],
        {
            "customer_id": types.PrimString("customer.id")
        },
        [types.PrimInt("payment_source.last4")],
        [[
            "\\customer_id -> {",
            "let x0 = /v1/customers/{customer}/sources_GET(customer=customer_id)",
            "x1 <- x0.data",
            "return x1.last4",
            "}"
        ]]
    ),
    TestCase(
        "2.12",
        "Delete a card for a customer",
        [],
        {
            "payment_method": types.PrimString("payment_method")
        },
        [types.SchemaObject("payment_source")],
        [[
            "\\customer_id => {",
            "let x1 = /v1/customers/{customer}_GET(customer=customer_id)",
            "let x2 = customer.default_source",
            "let x3 = /v1/customers/{customer}/sources/{source}_DELETE(customer=customer_id, source=x2)",
            "return x3",
            "}"
        ]]
    ),
    TestCase(
        "2.13",
        "Update payment methods of a customer for all subscriptions",
        [],
        {
            "payment_method": types.PrimString("payment_method"),
            "customer_id": types.PrimString("customer.id")
        },
        [types.ArrayType(None, types.SchemaObject("subscription"))],
        [[
            "(payment, customer_id) => {",
            "let x1 = /v1/subscriptions_GET(customer=customer_id)",
            "x2 <- x1.map(",
            "let x3 = /v1/subscriptions/{subscription}_POST(subscription=x2.id, default_payment_method=payment);",
            "return x3",
            "}"
        ]]
    )
])

square_bench = Benchmark("square", "configs/square_config.json",
[
 TestCase(
   "3.1",
   "List invoices that match location id",
   [],
   {
     "location_id": types.PrimString("Location.id")
   },
   [types.ArrayType(None, types.SchemaObject("Invoice"))],
   [[
     "\\location_id -> {",
     "let x0 = /v2/invoices_GET(location_id=location_id)",
     "x1 <- x0.invoices",
     "if x1.location_id = location_id",
     "return x1",
     "}"
   ]],
   8
 ),
 TestCase(
   "3.2",
   "Find subscription from location, customer, and plan id",
   [],
   {
     "customer_id": types.PrimString("Customer.id"),
     "location_id": types.PrimString("Location.id"),
     "subscription_plan_id": types.PrimString("CatalogObject.id")
   },
   [types.ArrayType(None, types.SchemaObject("Subscription"))],
   [[
     "\\customer_id location_id subscription_plan_id -> {",
     "let x0 = /v2/subscriptions/search_POST()",
     "x1 <- x0.subscriptions",
     "if x1.customer_id = customer_id",
     "if x1.customer_id = customer_id",
     "if x1.plan_id = subscription_plan_id",
     "if x1.location_id = location_id",
     "return x1",
     "}"
   ], [
     "\\customer_id location_id subscription_plan_id -> {",
     "let x0 = /v2/subscriptions/search_POST()",
     "x1 <- x0.subscriptions",
     "if x1.location_id = location_id",
     "if x1.location_id = location_id",
     "if x1.plan_id = subscription_plan_id",
     "if x1.customer_id = customer_id",
     "return x1",
     "}"
   ]],
   12
 ),
 TestCase(
   "3.3",
   "Get all items tax applies to",
   [],
   {
     "tax_id": types.PrimString("CatalogObject.id")
   },
   [types.ArrayType(None, types.SchemaObject("CatalogObject"))],
   [[
     "\\tax_id -> {",
     "let x0 = /v2/catalog/batch-retrieve_POST()",
     "x1 <- x0",
     "if x1.tax_id = tax_id",
     "}"
   ]],
   8
 ),
 TestCase(
   "3.4",
   "List discounts in catalog",
   [],
   {
   },
   [types.ArrayType(None, types.PrimString("CatalogDiscount.name"))],
   [[
     "\\ => {",
     "let x0 = /v2/catalog/batch-retrieve_POST()",
     "x1 <- x0",
     "return x1.discount_type",
     "}"
   ]],
   8
 ),
 TestCase(
   "3.5",
   "Delete catalog items with [names]",
   [],
   {
     "item_type": types.PrimString("CatalogObject.type"),
     "names": types.ArrayType(None, types.PrimString("CatalogDiscount.name"))
   },
   [types.SchemaObject("unknown_obj.deleted_object_ids")],
   [[
     "\\item_type, names => {",
     "let x0 = names.map(name => {",
     "let x1 = /v2/catalog/search-catalog-items_POST({",
     "object_types: [item_type],",
     "query: {",
     "exact_query: {",
     "attribute_name: \"name\",",
     "attribute_value: name",
     "}",
     "}",
     "})",
     "x2 <- x1",
     "./v2/catalog/batch-delete({",
     "object_ids: x2.id",
     "})",
     "return x1",
     "})",
     "return x0",
     "}"
   ]],
   10
 ),
TestCase(
  "3.6",
  "Delete all catalog items",
  [],
  {
  },
  [types.SchemaObject("unknown_obj.deleted_object_ids")],
  [[
    "\\ -> {",
    "let x0 = /v2/catalog/batch-retrieve_POST()",
    "x1 <- x0",
    "/v2/catalog/batch-delete_POST(object_ids = x1)",
    "}"
  ]],
  6
),
TestCase(
  "3.7",
  "Add order details to order",
  [],
  {
    "location_id": types.PrimString("Location.id"),
    "order_ids": types.ArrayType(None, types.PrimString("OrderLineItem.uid")),
    "updates": types.ArrayType(None, types.SchemaObject("OrderLineItem"))
  },
  [types.ArrayType(None, types.SchemaObject("OrderLineItem"))],
  [[
    "\\location_id, order_id, updates => {",
    "let x0 = /v2/orders/batch-retrieve_POST(location_id = location_id, order_ids: order_id)",
    "x1 <- x0",
    "let x2 = /v2/orders_POST(order_id = x1, order = update)",
    "return x2",
    "}"
  ]],
  8
),
TestCase(
  "3.8",
  "Get payment notes",
  [],
  {
  },
  [types.ArrayType(None, types.PrimString("Tender.note"))],
  [[
    "\\ -> {",
    "let x0 = /v2/payments_GET()",
    "x1 <- x0.payments",
    "return x1.note",
    "}"
  ]],
  8
),
TestCase(
  "3.9",
  "Get payment notes",
  [],
  {
    "location_id": types.PrimString("Location.id")
  },
  [types.ArrayType(None, types.PrimString("Transaction.order_id"))],
  [[
    "\\location_id -> {",
    "let x0 = /v2/locations/{location_id}/transactions_GET(location_id=location_id)",
    "x1 <- x0.transactions",
    "return x1.order_id",
    "}"
  ]],
  8
),
TestCase(
  "3.10",
  "Get product details (names of orders) from transaction id",
  [],
  {
    "location_id": types.PrimString("Location.id"),
    "transaction_id": types.PrimString("Transaction.id")
  },
  [types.ArrayType(None, types.PrimString("DeviceCode.name"))],
  [[
    "\\location_id, transaction_id => {",
    "let x0 = /v2/orders/batch-retrieve_POST(locationId = location_id, orderIds = [transaction_id])",
    "x1 <- x0",
    "x2 <- x1.line_items",
    "return item.name",
    "}"
  ]],
  10
),
TestCase(
  "3.11",
  "Search customers by name",
  [],
  {
    "name": types.PrimString("Customer.given_name")
  },
  [types.SchemaObject("Customer")],
  [[
    "\\name -> {",
    "let x0 = /v2/customers_GET()",
    "x1 <- x0.customers",
    "if x1.given_name = name",
    "return x1",
    "}"
  ]],
  10
)
])

benchmarks = [
  slack_bench,
  stripe_bench,
  square_bench
]
