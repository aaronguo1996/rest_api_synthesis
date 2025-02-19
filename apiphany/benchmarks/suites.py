from benchmarks.benchmark import Benchmark, BenchmarkSuite
from schemas import types
from program.program import (Program, ProjectionExpr, EquiExpr, ObjectExpr,
                            AssignExpr, VarExpr, AppExpr)

################################################################################
##                                  SLACK                                     ##
################################################################################

slack_minimal = [
    Benchmark(
        "1.5",
        "Create a channel and invite users",
        "https://stackoverflow.com/questions/48328380/slack-api-channels-create-followed-by-channels-invite-info-returns-channel-not",
        {
            "user_ids": types.ArrayType(None, types.PrimString("defs_user_id")),
            "channel_name": types.PrimString("objs_conversation.name"),
        },
        types.ArrayType(None, types.SchemaObject("objs_conversation")),
        [
            Program(
                ["user_ids", "channel_name"],
                [
                    AssignExpr("x0", AppExpr("/conversations.create_POST", [("name", VarExpr("channel_name"))]), False),
                    AssignExpr("x1", VarExpr("user_ids"), True),
                    AssignExpr("x2", AppExpr("/conversations.invite_POST", [("channel", ProjectionExpr(ProjectionExpr(VarExpr("x0"), "channel"), "id")), ("users", VarExpr("x1"))]), False),
                    ProjectionExpr(VarExpr("x2"), "channel")
                ]
            )
        ],
        True,
    ),
]

slack_benchmarks = [
    Benchmark(
        "1.1",
        "Retrieve emails of all members in a channel",
        "https://stackoverflow.com/questions/41564027/slack-api-retrieve-all-member-emails-from-a-slack-channel",
        {
            "channel_name": types.PrimString("objs_conversation.name")
        },
        types.ArrayType(None, types.PrimString("objs_user_profile.email")),
        [
            Program(
                ["channel_name"],
                [
                    AssignExpr("x0", AppExpr("/conversations.list_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "channels"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "name"), VarExpr("channel_name")),
                    AssignExpr("x2", AppExpr("/conversations.members_GET", [("channel", ProjectionExpr(VarExpr("x1"), "id"))]), False),
                    AssignExpr("x3", ProjectionExpr(VarExpr("x2"), "members"), True),
                    AssignExpr("x4", AppExpr("/users.profile.get_GET", [("user", VarExpr("x3"))]), False),
                    ProjectionExpr(ProjectionExpr(VarExpr("x4"), "profile"), "email"),
                ]
            ),
        ],
        False,
    ),
    Benchmark(
        "1.2",
        "Send a message to a user given their email",
        "https://stackoverflow.com/questions/43733375/slack-api-post-message-via-user-email",
        {
            "email": types.PrimString("objs_user_profile.email")
        },
        types.SchemaObject("objs_message"),
        [
            Program(
                ["email"],
                [
                    AssignExpr("x0", AppExpr("/users.lookupByEmail_GET", [("email", VarExpr("email"))]), False),
                    AssignExpr("x1", AppExpr("/conversations.open_POST", [("users", ProjectionExpr(ProjectionExpr(VarExpr("x0"), "user"), "id"))]), False),
                    AssignExpr("x2", AppExpr("/chat.postMessage_POST", [("channel", ProjectionExpr(ProjectionExpr(VarExpr("x1"), "channel"), "id"))]), False),
                    ProjectionExpr(VarExpr("x2"), "message"),
                ]
            ),
        ],
        True,
    ),
    Benchmark(
        "1.3",
        "Get the unread messages of a user",
        "https://stackoverflow.com/questions/64561594/is-it-possible-to-know-the-number-of-unread-slack-messages-a-user-has-with-the-s",
        {
            "user_id": types.PrimString("defs_user_id")
        },
        types.ArrayType(None, types.ArrayType(None, types.SchemaObject("objs_message"))),
        [
            Program(
                ["user_id"],
                [
                    AssignExpr("x0", AppExpr("/users.conversations_GET", [("user", VarExpr("user_id"))]), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "channels"), True),
                    AssignExpr("x2", AppExpr("/conversations.info_GET", [("channel", ProjectionExpr(VarExpr("x1"), "id"))]), False),
                    AssignExpr("x3", AppExpr("/conversations.history_GET", [("channel", ProjectionExpr(ProjectionExpr(VarExpr("x2"), "channel"), "id")), ("oldest", ProjectionExpr(ProjectionExpr(VarExpr("x2"), "channel"), "last_read"))]), False),
                    ProjectionExpr(VarExpr("x3"), "messages")
                ]
            ),
        ],
        False,
    ),
    Benchmark(
        "1.4",
        "Get all messages associated with a user",
        "https://github.com/hisabimbola/slack-history-export/blob/e53868d8820ba65e5e726bd5968c80d5eb54c0db/src/utils.js",
        {
            "user_id": types.PrimString("defs_user_id"),
            "ts": types.PrimString("defs_ts"),
        },
        types.ArrayType(None, types.SchemaObject("objs_message")),
        [
            Program(
                ["user_id", "ts"],
                [
                    AssignExpr("x0", AppExpr("/conversations.list_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "channels"), True),
                    AssignExpr("x2", AppExpr("/conversations.history_GET", [("channel", ProjectionExpr(VarExpr("x1"), "id")), ("oldest", VarExpr("ts"))]), False),
                    AssignExpr("x3", ProjectionExpr(VarExpr("x2"), "messages"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x3"), "user"), VarExpr("user_id")),
                    VarExpr("x3")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "1.5",
        "Create a channel and invite a list of users",
        "https://stackoverflow.com/questions/48328380/slack-api-channels-create-followed-by-channels-invite-info-returns-channel-not",
        {
            "user_ids": types.ArrayType(None, types.PrimString("defs_user_id")),
            "channel_name": types.PrimString("objs_conversation.name"),
        },
        types.ArrayType(None, types.SchemaObject("objs_conversation")),
        [
            Program(
                ["user_ids", "channel_name"],
                [
                    AssignExpr("x0", AppExpr("/conversations.create_POST", [("name", VarExpr("channel_name"))]), False),
                    AssignExpr("x1", VarExpr("user_ids"), True),
                    AssignExpr("x2", AppExpr("/conversations.invite_POST", [("channel", ProjectionExpr(ProjectionExpr(VarExpr("x0"), "channel"), "id")), ("users", VarExpr("x1"))]), False),
                    ProjectionExpr(VarExpr("x2"), "channel")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "1.6",
        "Reply to a message and update it",
        None,
        {
            "channel": types.PrimString("defs_channel"),
            "ts": types.PrimString("defs_ts"),
        },
        types.SchemaObject("objs_message"),
        [
            Program(
                ["channel", "ts"],
                [
                    AssignExpr("x1", AppExpr("/chat.postMessage_POST", [("channel", VarExpr("channel")), ("thread_ts", VarExpr("ts"))]), False),
                    AssignExpr("x2", AppExpr("/chat.update_POST", [("channel", VarExpr("channel")), ("ts", ProjectionExpr(VarExpr("x1"), "ts"))]), False),
                    ProjectionExpr(VarExpr("x2"), "message")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "1.7",
        "Send a message to a channel with the given name",
        "https://github.com/backspace/slack-statsbot/blob/primary/src/statsbot.js",
        {
            "channel": types.PrimString("objs_conversation.name"),
        },
        types.SchemaObject("objs_message"),
        [
            Program(
                ["channel"],
                [
                    AssignExpr("x0", AppExpr("/conversations.list_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "channels"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "name"), VarExpr("channel")),
                    AssignExpr("x2", AppExpr("/chat.postMessage_POST", [("channel", ProjectionExpr(VarExpr("x1"), "id"))]), False),
                    ProjectionExpr(VarExpr("x2"), "message")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "1.8",
        "Get the unread messages of a channel",
        "https://stackoverflow.com/questions/64561594/is-it-possible-to-know-the-number-of-unread-slack-messages-a-user-has-with-the-s",
        {
            "channel_id": types.PrimString("defs_channel")
        },
        types.ArrayType(None, types.ArrayType(None, types.SchemaObject("objs_message"))),
        [
            Program(
                ["channel_id"],
                [
                    AssignExpr("x2", AppExpr("/conversations.info_GET", [("channel", VarExpr("channel_id"))]), False),
                    AssignExpr("x3", AppExpr("/conversations.history_GET", [("channel", VarExpr("channel_id")), ("oldest", ProjectionExpr(ProjectionExpr(VarExpr("x2"), "channel"), "last_read"))]), False),
                    ProjectionExpr(VarExpr("x3"), "messages")
                ]
            ),
        ],
        False,
    ),
]

slack_suite = BenchmarkSuite(
    "configs/slack_config.json",
    "slack",
    slack_benchmarks
)


################################################################################
##                                  STRIPE                                    ##
################################################################################

stripe_minimal = [
    Benchmark(
        "2.1",
        "Make a subscription to a product for a customer",
        "https://github.com/stripe-samples/charging-for-multiple-plan-subscriptions/blob/master/server/node/server.js",
        {
            "customer_id": types.PrimString("customer.id"),
            "product_id": types.PrimString("product.id"),
        },
        types.ArrayType(None, types.SchemaObject("subscription")),
        [
            Program(
                ["customer_id", "product_id"],
                [
                    AssignExpr("x1", AppExpr("/v1/prices_GET", [("product", VarExpr("product_id"))]), False),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "data"), True),
                    AssignExpr("x3", AppExpr("/v1/subscriptions_POST", [("customer", VarExpr("customer_id")), ("items[0][price]", ProjectionExpr(VarExpr("x2"), "id"))]), False),
                    VarExpr("x3")
                ]
            )
        ],
        True,
    ),
]

stripe_benchmarks = [
    Benchmark(
        "2.1",
        "Subscribe to a product for a customer",
        "https://github.com/stripe-samples/charging-for-multiple-plan-subscriptions/blob/master/server/node/server.js",
        {
            "customer_id": types.PrimString("customer.id"),
            "product_id": types.PrimString("product.id"),
        },
        types.ArrayType(None, types.SchemaObject("subscription")),
        [
            Program(
                ["customer_id", "product_id"],
                [
                    AssignExpr("x1", AppExpr("/v1/prices_GET", [("product", VarExpr("product_id"))]), False),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "data"), True),
                    AssignExpr("x3", AppExpr("/v1/subscriptions_POST", [("customer", VarExpr("customer_id")), ("items[0][price]", ProjectionExpr(VarExpr("x2"), "id"))]), False),
                    VarExpr("x3")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "2.2",
        "Subscribe to multiple items",
        "https://github.com/stripe-samples/charging-for-multiple-plan-subscriptions/blob/master/server/node/server.js",
        {
            "customer_id": types.PrimString("customer.id"),
            "product_ids": types.ArrayType(None, types.PrimString("product.id")),
        },
        types.ArrayType(None, types.SchemaObject("subscription")),
        [
            Program(
                ["customer_id", "product_ids"],
                [
                    AssignExpr("x0", VarExpr("product_ids"), True),
                    AssignExpr("x1", AppExpr("/v1/prices_GET", [("product", VarExpr("x0"))]), False),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "data"), True),
                    AssignExpr("x3", AppExpr("/v1/subscriptions_POST", [("customer", VarExpr("customer_id")), ("items[0][price]", ProjectionExpr(VarExpr("x2"), "id"))]), False),
                    VarExpr("x3")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "2.3",
        "Create a product and invoice a customer",
        "https://stripe.com/docs/invoicing/prices-guide",
        {
            "product_name": types.PrimString("product.name"),
            "customer_id": types.PrimString("customer.id"),
            "currency": types.PrimString("fee.currency"),
            "unit_amount": types.PrimInt("plan.amount"),
        },
        types.SchemaObject("invoiceitem"),
        [
            Program(
                ["product_name", "customer_id", "currency", "unit_amount"],
                [
                    AssignExpr("x0", AppExpr("/v1/products_POST", [("name", VarExpr("product_name"))]), False),
                    AssignExpr("x1", AppExpr("/v1/prices_POST", [("currency", VarExpr("currency")), ("product", ProjectionExpr(VarExpr("x0"), "id")), ("unit_amount", VarExpr("unit_amount"))]), False),
                    AssignExpr("x2", AppExpr("/v1/invoiceitems_POST", [("customer", VarExpr("customer_id")), ("price", ProjectionExpr(VarExpr("x1"), "id"))]), False),
                    VarExpr("x2")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "2.4",
        "Retrieve a customer by email",
        "https://stackoverflow.com/questions/26767150/stripe-is-it-possible-to-search-a-customer-by-their-email",
        {
            "email": types.PrimString("customer.email"),
        },
        types.SchemaObject("customer"),
        [
            Program(
                ["email"],
                [
                    AssignExpr("x0", AppExpr("/v1/customers_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "data"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "email"), VarExpr("email")),
                    VarExpr("x1")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "2.5",
        "Get a list of receipts for a customer",
        "https://stackoverflow.com/questions/24335268/stripe-api-receipts-listing",
        {
            "customer_id": types.PrimString("customer.id"),
        },
        types.ArrayType(None, types.SchemaObject("charge")),
        [
            Program(
                ["customer_id"],
                [
                    AssignExpr("x1", AppExpr("/v1/invoices_GET", [("customer", VarExpr("customer_id"))]), False),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "data"), True),
                    AssignExpr("x3", AppExpr("/v1/charges/{charge}_GET", [("charge", ProjectionExpr(VarExpr("x2"), "charge"))]), False),
                    VarExpr("x3")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "2.6",
        "Get a refund for a subscription",
        "https://stackoverflow.com/questions/62403075/stripe-api-get-upcoming-invoice-for-cancelled-subscription",
        {
            "subscription": types.PrimString("subscription.id"),
        },
        types.SchemaObject("refund"),
        [
            Program(
                ["subscription"],
                [
                    AssignExpr("x0", AppExpr("/v1/subscriptions/{subscription_exposed_id}_GET", [("subscription_exposed_id", VarExpr("subscription"))]), False),
                    AssignExpr("x1", AppExpr("/v1/invoices/{invoice}_GET", [("invoice", ProjectionExpr(VarExpr("x0"), "latest_invoice"))]), False),
                    AssignExpr("x2", AppExpr("/v1/refunds_POST", [("charge", ProjectionExpr(VarExpr("x1"), "charge"))]), False),
                    VarExpr("x2")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "2.7",
        "Get the emails of all customers",
        "https://stackoverflow.com/questions/65545997/python3-stripe-api-to-get-all-customer-email",
        {
        },
        types.ArrayType(None, types.PrimString("customer.email")),
        [
            Program(
                [],
                [
                    AssignExpr("x0", AppExpr("/v1/customers_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "data"), True),
                    ProjectionExpr(VarExpr("x1"), "email")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "2.8",
        "Get the emails of the subscribers of a product",
        "https://stackoverflow.com/questions/35882771/use-stripe-api-to-return-a-list-of-valid-subscribers",
        {
            "product_id": types.PrimString("product.id"),
        },
        types.ArrayType(None, types.PrimString("customer.email")),
        [
            Program(
                ["product_id"],
                [
                    AssignExpr("x1", AppExpr("/v1/subscriptions_GET", []), False),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "data"), True),
                    AssignExpr("x3", ProjectionExpr(ProjectionExpr(VarExpr("x2"), "items"), "data"), True),
                    EquiExpr(ProjectionExpr(ProjectionExpr(VarExpr("x3"), "price"), "product"), VarExpr("product_id")),
                    AssignExpr("x4", AppExpr("/v1/customers/{customer}_GET", [("customer", ProjectionExpr(VarExpr("x2"), "customer"))]), False),
                    ProjectionExpr(VarExpr("x4"), "email")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "2.9",
        "Get the last 4 digits of a customer's card",
        "https://stackoverflow.com/questions/30447026/getting-last4-digits-of-card-using-customer-object-stripe-api-with-php",
        {
            "customer_id": types.PrimString("customer.id"),
        },
        types.PrimString("bank_account.last4"),
        [
            Program(
                ["customer_id"],
                [
                    AssignExpr("x0", AppExpr("/v1/customers/{customer}/sources_GET", [("customer", VarExpr("customer_id"))]), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "data"), True),
                    ProjectionExpr(VarExpr("x1"), "last4")
                    # ProjectionExpr(ProjectionExpr(VarExpr("x1"), "card"), "last4")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "2.10",
        "Update payment methods for a user's subscriptions",
        "https://stackoverflow.com/questions/58270828/update-credit-card-details-of-user-for-all-subscriptions-in-stripe-using-api",
        {
            "payment_method": types.SchemaObject("payment_method"),
            "customer_id": types.PrimString("customer.id"),
        },
        types.ArrayType(None, types.SchemaObject("subscription")),
        [
            Program(
                ["payment_method", "customer_id"],
                [
                    AssignExpr("x0", AppExpr("/v1/subscriptions_GET", [("customer", VarExpr("customer_id"))]), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "data"), True),
                    AssignExpr("x2", AppExpr("/v1/subscriptions/{subscription_exposed_id}_POST", [("subscription_exposed_id", ProjectionExpr(VarExpr("x1"), "id")), ("default_payment_method", ProjectionExpr(VarExpr("payment_method"), "id"))]), False),
                    VarExpr("x2")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "2.11",
        "Delete the default payment source for a customer",
        "https://stackoverflow.com/questions/17807881/stripe-api-throwing-error-when-trying-to-delete-a-card",
        {
            "customer_id": types.PrimString("customer.id"),
        },
        types.SchemaObject("payment_source"),
        [
            Program(
                ["customer_id"],
                [
                    AssignExpr("x0", AppExpr("/v1/customers/{customer}_GET", [("customer", VarExpr("customer_id"))]), False),
                    AssignExpr("x1", AppExpr("/v1/customers/{customer}/sources/{id}_DELETE", [("customer", VarExpr("customer_id")), ("id", ProjectionExpr(VarExpr("x0"), "default_source"))]), False),
                    VarExpr("x1")
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "2.12",
        "Save a card during payment",
        "https://github.com/stripe-samples/saving-card-after-payment/blob/master/without-webhooks/server/node/server.js",
        {
            "cur": types.PrimString("fee.currency"),
            "amt": types.PrimInt("plan.amount"),
            "pm": types.PrimString("payment_method.id"),
        },
        types.SchemaObject("payment_intent"),
        [
            Program(
                ["cur", "amt", "pm"],
                [
                    AssignExpr("x1", AppExpr("/v1/customers_POST", []), False),
                    AssignExpr("x2", AppExpr("/v1/payment_intents_POST", [("customer", ProjectionExpr(VarExpr("x1"), "id")), ("payment_method", VarExpr("pm")), ("currency", VarExpr("cur")), ("amount", VarExpr("amt"))]), False),
                    AssignExpr("x3", AppExpr("/v1/payment_intents/{intent}/confirm_POST", [("intent", ProjectionExpr(VarExpr("x2"), "id"))]), False),
                    VarExpr("x3")
                ]
            ),
        ],
        True,
    ),
    Benchmark(
        "2.13",
        "Send an invoice to a customer",
        "https://stripe.com/docs/invoicing/integration#send-invoice",
        {
            "customer_id": types.PrimString("customer.id"),
            "price_id": types.PrimString("plan.id"),
        },
        types.SchemaObject("invoice"),
        [
            Program(
                ["customer_id", "price_id"],
                [
                    AssignExpr("x1", AppExpr("/v1/invoiceitems_POST", [("customer", VarExpr("customer_id")), ("price", VarExpr("price_id"))]), False),
                    AssignExpr("x2", AppExpr("/v1/invoices_POST", [("customer", ProjectionExpr(VarExpr("x1"), "customer"))]), False),
                    AssignExpr("x3", AppExpr("/v1/invoices/{invoice}/send_POST", [("invoice", ProjectionExpr(VarExpr("x2"), "id"))]), False),
                    VarExpr("x3")
                ]
            )
        ],
        True,
    ),
]

stripe_suite = BenchmarkSuite(
    "configs/stripe_config.json",
    "stripe",
    stripe_benchmarks
)

################################################################################
##                                  SQUARE                                    ##
################################################################################

square_minimal = [
    Benchmark(
        "3.1",
        "List invoices that match location id",
        "https://github.com/square/connect-api-examples/blob/4283ac967c31b75dc17aceebd84f649093477e9a/connect-examples/v2/node_invoices/routes/management.js",
        {
            "location_id": types.PrimString("Location.id"),
        },
        types.ArrayType(None, types.SchemaObject("Invoice")),
        [
            Program(
                ["location_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/invoices_GET", [("location_id", VarExpr("location_id"))]), False),
                    ProjectionExpr(VarExpr("x0"), "invoices")
                ]
            )
        ],
        False,
    ),
]

square_benchmarks = [
    Benchmark(
        "3.1",
        "List invoices that match a location id",
        "https://github.com/square/connect-api-examples/blob/4283ac967c31b75dc17aceebd84f649093477e9a/connect-examples/v2/node_invoices/routes/management.js",
        {
            "location_id": types.PrimString("Location.id"),
        },
        types.ArrayType(None, types.SchemaObject("Invoice")),
        [
            Program(
                ["location_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/invoices_GET", [("location_id", VarExpr("location_id"))]), False),
                    ProjectionExpr(VarExpr("x0"), "invoices")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.2",
        "List subscriptions by location, customer, and plan",
        "https://github.com/square/connect-api-examples/blob/4283ac967c31b75dc17aceebd84f649093477e9a/connect-examples/v2/node_subscription/routes/subscription.js",
        {
            "customer_id": types.PrimString("Customer.id"),
            "location_id": types.PrimString("Location.id"),
            "plan_id": types.PrimString("CatalogObject.id"),
        },
        types.ArrayType(None, types.SchemaObject("Subscription")),
        [
            Program(
                ["customer_id", "location_id", "plan_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/subscriptions/search_POST", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "subscriptions"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "customer_id"), VarExpr("customer_id")),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "location_id"), VarExpr("location_id")),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "plan_id"), VarExpr("plan_id")),
                    VarExpr("x1")
                ]
            ),
            Program(
                ["customer_id", "location_id", "plan_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/subscriptions/search_POST", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "subscriptions"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "location_id"), VarExpr("location_id")),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "customer_id"), VarExpr("customer_id")),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "plan_id"), VarExpr("plan_id")),
                    VarExpr("x1")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.3",
        "Get all items a tax applies to",
        "https://github.com/square/catalog-api-demo/blob/85b6754c90fa7b66fc5e605ee7a344314537eade/src/main/java/com/squareup/catalog/demo/example/ApplyTaxToAllIItemsExample.java",
        {
            "tax_id": types.PrimString("CatalogObject.id"),
        },
        types.ArrayType(None, types.SchemaObject("CatalogObject")),
        [
            Program(
                ["tax_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/catalog/search_POST", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "objects"), True),
                    AssignExpr("x2", ProjectionExpr(ProjectionExpr(VarExpr("x1"), "item_data"), "tax_ids"), True),
                    EquiExpr(VarExpr("x2"), VarExpr("tax_id")),
                    VarExpr("x1")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.4",
        "Get a list of discounts in the catalog",
        "https://github.com/square/catalog-api-demo/blob/master/src/main/java/com/squareup/catalog/demo/example/ListDiscountsExample.java",
        {
        },
        types.ArrayType(None, types.PrimString("CatalogDiscount")),
        [
            Program(
                [],
                [
                    AssignExpr("x0", AppExpr("/v2/catalog/list_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "objects"), True),
                    ProjectionExpr(VarExpr("x1"), "discount_data")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.5",
        "Add order details to order",
        "https://github.com/square/connect-api-examples/blob/4283ac967c31b75dc17aceebd84f649093477e9a/connect-examples/v2/node_orders-payments/routes/checkout.js",
        {
            "location_id": types.PrimString("Location.id"),
            "order_ids": types.ArrayType(None, types.PrimString("Order.id")),
            "updates": types.ArrayType(None, types.SchemaObject("OrderFulfillment")),
        },
        types.ArrayType(None, types.SchemaObject("Order")),
        [
            Program(
                ["location_id", "order_ids", "updates"],
                [
                    AssignExpr("x0", VarExpr("order_ids"), True),
                    AssignExpr("x1", AppExpr("/v2/orders/batch-retrieve_POST", [("location_id", VarExpr("location_id")), ("order_ids[0]", VarExpr("x0"))]), False),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "orders"), True),
                    AssignExpr("x3", ObjectExpr({"fulfillments": VarExpr("updates")}), False),
                    AssignExpr("x4", AppExpr("/v2/orders/{order_id}_PUT", [("order_id", ProjectionExpr(VarExpr("x2"), "id")), ("order", VarExpr("x3"))]), False),
                    ProjectionExpr(VarExpr("x4"), "order"),
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "3.6",
        "Get payment notes of a payment",
        "https://stackoverflow.com/questions/23252751/square-connect-api-list-payments-endpoint-not-showing-description",
        {
        },
        types.ArrayType(None, types.PrimString("Payment.note")),
        [
            Program(
                [],
                [
                    AssignExpr("x0", AppExpr("/v2/payments_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "payments"), True),
                    ProjectionExpr(VarExpr("x1"), "note")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.7",
        "Get order ids of current user's transactions",
        "https://stackoverflow.com/questions/46910044/getting-compact-information-from-square-connect-api",
        {
            "location_id": types.PrimString("Location.id"),
        },
        types.ArrayType(None, types.PrimString("Order.id")),
        [
            Program(
                ["location_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/locations/{location_id}/transactions_GET", [("location_id", VarExpr("location_id"))]), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "transactions"), True),
                    ProjectionExpr(VarExpr("x1"), "order_id"),
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.8",
        "Get order names from a transaction id",
        "https://stackoverflow.com/questions/58047894/square-connect-how-to-retrieve-product-information-from-transaction-id",
        {
            "location_id": types.PrimString("Location.id"),
            "transaction_id": types.PrimString("Order.id"),
        },
        types.ArrayType(None, types.PrimString("Invoice.title")),
        [
            Program(
                ["location_id", "transaction_id"],
                [
                    AssignExpr("x0", AppExpr("/v2/orders/batch-retrieve_POST", [("location_id", VarExpr("location_id")), ("order_ids[0]", VarExpr("transaction_id"))]), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "orders"), True),
                    AssignExpr("x2", ProjectionExpr(VarExpr("x1"), "line_items"), True),
                    ProjectionExpr(VarExpr("x2"), "name"),
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.9",
        "Find customers by name",
        "https://developer.squareup.com/forums/t/search-customers-by-name/1567",
        {
            "name": types.PrimString("Customer.given_name"),
        },
        types.SchemaObject("Customer"),
        [
            Program(
                ["name"],
                [
                    AssignExpr("x0", AppExpr("/v2/customers_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "customers"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "given_name"), VarExpr("name")),
                    VarExpr("x1")
                ]
            ),
            Program(
                ["name"],
                [
                    AssignExpr("x0", AppExpr("/v2/customers/search_POST", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "customers"), True),
                    EquiExpr(ProjectionExpr(VarExpr("x1"), "given_name"), VarExpr("name")),
                    VarExpr("x1")
                ]
            )
        ],
        False,
    ),
    Benchmark(
        "3.10",
        "Delete catalog items with names",
        "https://github.com/square/catalog-api-demo/blob/85b6754c90fa7b66fc5e605ee7a344314537eade/src/main/java/com/squareup/catalog/demo/example/DeleteCategoryExample.java",
        {
            "item_type": types.PrimString("CatalogObject.type"),
            "names": types.ArrayType(None, types.PrimString("CatalogItem.name"))
        },
        # types.SchemaObject("DeleteCatalogObjectResponse"),
        types.ArrayType(None, types.PrimString("CatalogObject.id")),
        [
            Program(
                ["item_type", "names"],
                [
                    AssignExpr("x0", AppExpr("/v2/catalog/search_POST", [("object_types[0]", VarExpr("item_type"))]), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "objects"), True),
                    AssignExpr("x2", VarExpr("names"), True),
                    EquiExpr(ProjectionExpr(ProjectionExpr(VarExpr("x1"), "item_data"), "name"), VarExpr("x2")),
                    AssignExpr("x3", AppExpr("/v2/catalog/object/{object_id}_DELETE", [("object_id", ProjectionExpr(VarExpr("x1"), "id"))]), False),
                    AssignExpr("x4", ProjectionExpr(VarExpr("x3"), "deleted_object_ids"), True),
                    VarExpr("x4"),
                ]
            )
        ],
        True,
    ),
    Benchmark(
        "3.11",
        "Delete all catalog items",
        "https://github.com/square/catalog-api-demo/blob/85b6754c90fa7b66fc5e605ee7a344314537eade/src/main/java/com/squareup/catalog/demo/example/DeleteAllItemsExample.java",
        {
        },
        types.ArrayType(None, types.PrimString("CatalogObject.id")),
        [
            Program(
                [],
                [
                    AssignExpr("x0", AppExpr("/v2/catalog/list_GET", []), False),
                    AssignExpr("x1", ProjectionExpr(VarExpr("x0"), "objects"), True),
                    AssignExpr("x2", AppExpr("/v2/catalog/object/{object_id}_DELETE", [("object_id", ProjectionExpr(VarExpr("x1"), "id"))]), False),
                    ProjectionExpr(VarExpr("x2"), "deleted_object_ids"),
                ]
            )
        ],
        True,
    ),
]

square_suite = BenchmarkSuite(
    "configs/square_config.json",
    "squareapi",
    square_benchmarks
)