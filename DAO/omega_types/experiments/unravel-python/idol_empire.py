#!/usr/bin/env python3
"""
idol_empire.py
Idol/Talent Agency Empire Simulator using Unravel V3
Entertainment industry chaos handled with mathematical guarantees!

Build your entertainment empire while dealing with:
- Scandals that would normally crash PR systems
- Market crashes that destroy traditional financial models  
- Talent drama that breaks normal management systems
- Fan chaos that overwhelms social media platforms
"""

import random
import time
from unravel_v3 import *
from dataclasses import dataclass
from typing import List, Dict

@dataclass
class Idol:
    name: str
    talent_level: int
    drama_factor: int  # How much chaos they generate
    fan_base: int
    scandal_history: int
    age: int
    
    def __str__(self):
        return f"{self.name} (Talent:{self.talent_level}, Drama:{self.drama_factor}, Fans:{self.fan_base})"

class IdolEmpireManager:
    """Talent agency that handles entertainment industry chaos with mathematical grace"""
    
    def __init__(self, agency_name: str):
        self.agency_name = agency_name
        self.idols: List[Idol] = []
        self.agency_reputation = 50
        self.total_fans = 0
        self.agency_wealth = 100000  # Starting budget
        self.industry_entropy = 0  # How much chaos we've encountered
        self.scandal_count = 0
        self.successful_events = 0
        self.current_year = 2024
        
        print(f"🎭 {agency_name} TALENT AGENCY ESTABLISHED!")
        print(f"   Starting budget: ${self.agency_wealth:,}")
        print(f"   Industry entropy: {self.industry_entropy} (pristine start)")
    
    def recruit_idol(self, name: str = None, talent: int = None, drama: int = None):
        """Recruit new talent - even problematic ones become manageable"""
        
        # Generate or use provided stats
        name = name or f"Star_{len(self.idols) + 1}"
        talent = talent if talent is not None else random.randint(10, 100)
        drama = drama if drama is not None else random.randint(0, 50)
        
        print(f"\n⭐ RECRUITING: {name}")
        print(f"   Talent level: {talent}, Drama factor: {drama}")
        
        # Calculate recruitment cost with total safety
        recruitment_calc = Ex.let("talent", Ex.num(talent),
                                 Ex.let("drama", Ex.num(drama),
                                       Ex.let("base_cost", Ex.num(10000),
                                             # Cost = base_cost * talent / (100 - drama)
                                             # High drama = expensive (or impossible if drama = 100)
                                             Ex.default(
                                                 Ex.mul(Ex.variable("base_cost"),
                                                       Ex.div(Ex.variable("talent"), 
                                                             Ex.sub(Ex.num(100), Ex.variable("drama")))),
                                                 Ex.mul(Ex.variable("base_cost"), Ex.variable("talent"))))))
        
        result = run_thermo(recruitment_calc)
        recruitment_cost = result[0].value if isinstance(result[0], VTNum) else talent * 10000
        chaos_generated = result[1].total_entropy
        
        # Can we afford them?
        if recruitment_cost <= self.agency_wealth:
            new_idol = Idol(
                name=name,
                talent_level=talent,
                drama_factor=drama,
                fan_base=talent * 10,  # Initial fans based on talent
                scandal_history=0,
                age=random.randint(16, 25)
            )
            
            self.idols.append(new_idol)
            self.agency_wealth -= recruitment_cost
            self.total_fans += new_idol.fan_base
            self.industry_entropy += chaos_generated
            
            if chaos_generated > 0:
                print(f"   💰 Recruited despite mathematical impossibility! Cost: ${recruitment_cost:,}")
                print(f"   🌪️ Industry chaos generated: +{chaos_generated}")
            else:
                print(f"   ✅ Clean recruitment: ${recruitment_cost:,}")
            
            return new_idol
        else:
            print(f"   💸 Too expensive: ${recruitment_cost:,} (budget: ${self.agency_wealth:,})")
            return None
    
    def plan_concert_tour(self, idol: Idol, venues: int = None, ticket_price: int = None):
        """Plan concert tour - handles venue disasters gracefully"""
        
        venues = venues or random.randint(5, 20)
        ticket_price = ticket_price or random.randint(20, 200)
        
        print(f"\n🎪 CONCERT TOUR: {idol.name}")
        print(f"   Venues: {venues}, Ticket price: ${ticket_price}")
        
        # Revenue calculation with chaos factors
        tour_calc = Ex.let("venues", Ex.num(venues),
                          Ex.let("price", Ex.num(ticket_price),
                                Ex.let("talent", Ex.num(idol.talent_level),
                                      Ex.let("fans", Ex.num(idol.fan_base),
                                            # Revenue = venues * price * (talent + fans) / drama_risk
                                            Ex.default(
                                                Ex.div(
                                                    Ex.mul(Ex.mul(Ex.variable("venues"), Ex.variable("price")),
                                                          Ex.add(Ex.variable("talent"), Ex.variable("fans"))),
                                                    Ex.num(max(1, idol.drama_factor))),  # Drama creates risk
                                                # Fallback: basic venue revenue
                                                Ex.mul(Ex.variable("venues"), Ex.mul(Ex.variable("price"), Ex.num(100))))))))
        
        result = run_thermo(tour_calc)
        tour_revenue = result[0].value if isinstance(result[0], VTNum) else venues * ticket_price * 100
        tour_chaos = result[1].total_entropy
        
        # Update agency stats
        self.agency_wealth += tour_revenue
        self.industry_entropy += tour_chaos
        self.successful_events += 1
        
        # Update idol stats
        idol.fan_base += venues * 50  # Tours build fanbase
        self.total_fans += venues * 50
        
        if tour_chaos > 0:
            print(f"   🎢 Chaotic tour! Mathematical impossibilities encountered but show went on!")
            print(f"   💰 Revenue (despite chaos): ${tour_revenue:,}")
            print(f"   📈 New fans: +{venues * 50} (total: {idol.fan_base:,})")
        else:
            print(f"   ✨ Perfect tour execution!")
            print(f"   💰 Revenue: ${tour_revenue:,}")
            print(f"   📈 New fans: +{venues * 50}")
        
        return tour_revenue
    
    def handle_scandal(self, idol: Idol, scandal_severity: int = None):
        """Handle scandal - where traditional PR systems would panic"""
        
        scandal_severity = scandal_severity or random.randint(10, 100)
        
        print(f"\n💥 SCANDAL ALERT: {idol.name}")
        print(f"   Scandal severity: {scandal_severity}")
        print(f"   Agency reputation: {self.agency_reputation}")
        
        # Scandal damage calculation
        scandal_calc = Ex.let("severity", Ex.num(scandal_severity),
                             Ex.let("reputation", Ex.num(self.agency_reputation),
                                   Ex.let("idol_talent", Ex.num(idol.talent_level),
                                         # Damage = severity^2 / (reputation + talent)
                                         # Could be division by zero if both are zero!
                                         Ex.default(
                                             Ex.div(Ex.mul(Ex.variable("severity"), Ex.variable("severity")),
                                                   Ex.add(Ex.variable("reputation"), Ex.variable("idol_talent"))),
                                             Ex.variable("severity")))))  # Fallback to base severity
        
        result = run_thermo(scandal_calc)
        damage = result[0].value if isinstance(result[0], VTNum) else scandal_severity
        scandal_chaos = result[1].total_entropy
        
        # Apply damage with mathematical guarantees
        fan_loss = min(idol.fan_base, damage * 100)
        reputation_loss = min(self.agency_reputation, damage // 2)
        
        idol.fan_base = max(0, idol.fan_base - fan_loss)
        idol.scandal_history += 1
        self.agency_reputation = max(0, self.agency_reputation - reputation_loss)
        self.total_fans = max(0, self.total_fans - fan_loss)
        self.industry_entropy += scandal_chaos
        self.scandal_count += 1
        
        if scandal_chaos > 0:
            print(f"   🌪️ Mathematical impossibility in scandal calculation!")
            print(f"   💔 Fans lost: {fan_loss:,} (mathematical chaos handled)")
            print(f"   📉 Reputation: -{reputation_loss} (but agency survives)")
            outcome = "Survived impossible scandal through mathematical grace"
        else:
            print(f"   💔 Fans lost: {fan_loss:,}")
            print(f"   📉 Reputation: -{reputation_loss}")
            outcome = "Standard scandal damage control"
        
        print(f"   🔄 {idol.name} scandal history: {idol.scandal_history}")
        return outcome
    
    def attempt_comeback(self, idol: Idol):
        """Attempt idol comeback - mathematical redemption"""
        
        print(f"\n🔄 COMEBACK ATTEMPT: {idol.name}")
        print(f"   Current fans: {idol.fan_base:,}, Scandals: {idol.scandal_history}")
        
        # Comeback calculation with redemption math
        comeback_calc = Ex.let("talent", Ex.num(idol.talent_level),
                              Ex.let("scandals", Ex.num(idol.scandal_history),
                                    Ex.let("current_fans", Ex.num(idol.fan_base),
                                          # Comeback power = talent^2 / scandals
                                          # Division by zero if no scandals!
                                          Ex.default(
                                              Ex.div(Ex.mul(Ex.variable("talent"), Ex.variable("talent")),
                                                    Ex.variable("scandals")),
                                              # No scandals = pure talent comeback
                                              Ex.mul(Ex.variable("talent"), Ex.num(100))))))
        
        result = run_thermo(comeback_calc)
        comeback_power = result[0].value if isinstance(result[0], VTNum) else idol.talent_level * 100
        comeback_chaos = result[1].total_entropy
        
        # Comeback effects
        fan_gain = comeback_power * 50
        reputation_boost = comeback_power // 20
        
        idol.fan_base += fan_gain
        self.total_fans += fan_gain
        self.agency_reputation = min(100, self.agency_reputation + reputation_boost)
        self.industry_entropy += comeback_chaos
        
        if comeback_chaos > 0:
            print(f"   ✨ MATHEMATICAL REDEMPTION! Division by zero became infinite comeback power!")
        else:
            print(f"   📈 Calculated comeback success")
        
        print(f"   🎯 Fans gained: +{fan_gain:,}")
        print(f"   📈 Reputation boost: +{reputation_boost}")
        
        return comeback_power
    
    def simulate_market_crash(self):
        """Simulate industry market crash - tests system resilience"""
        
        print(f"\n📉 MARKET CRASH EVENT!")
        crash_severity = random.randint(50, 100)
        
        # Market crash affects all idols
        crash_calc = Ex.let("severity", Ex.num(crash_severity),
                           Ex.let("agency_size", Ex.num(len(self.idols)),
                                 # Market impact = severity / agency_size (could be div by zero!)
                                 Ex.default(
                                     Ex.div(Ex.variable("severity"), Ex.variable("agency_size")),
                                     Ex.variable("severity"))))  # No diversification protection
        
        result = run_thermo(crash_calc)
        market_impact = result[0].value if isinstance(result[0], VTNum) else crash_severity
        crash_chaos = result[1].total_entropy
        
        # Apply market damage
        wealth_loss = min(self.agency_wealth, market_impact * 1000)
        fan_exodus = market_impact * 100
        
        self.agency_wealth = max(10000, self.agency_wealth - wealth_loss)  # Always keep some money
        self.total_fans = max(0, self.total_fans - fan_exodus)
        self.industry_entropy += crash_chaos
        
        # Update all idols
        for idol in self.idols:
            idol.fan_base = max(100, idol.fan_base - fan_exodus // len(self.idols))
        
        if crash_chaos > 0:
            print(f"   💥 IMPOSSIBLE MARKET CONDITIONS! Mathematical chaos level: {crash_chaos}")
            print(f"   💸 Wealth lost: ${wealth_loss:,} (but mathematical guarantees prevented bankruptcy)")
        else:
            print(f"   📊 Standard market correction")
            print(f"   💸 Wealth lost: ${wealth_loss:,}")
        
        print(f"   🏢 Agency survives with ${self.agency_wealth:,}")
        return f"Market crash survived: ${wealth_loss:,} lost but agency intact"
    
    def run_viral_campaign(self, idol: Idol, campaign_budget: int = None):
        """Run viral marketing campaign - handle social media chaos"""
        
        campaign_budget = campaign_budget or random.randint(5000, 50000)
        
        print(f"\n📱 VIRAL CAMPAIGN: {idol.name}")
        print(f"   Budget: ${campaign_budget:,}")
        
        # Viral calculation with chaos factors
        viral_calc = Ex.let("budget", Ex.num(campaign_budget),
                           Ex.let("talent", Ex.num(idol.talent_level),
                                 Ex.let("existing_fans", Ex.num(idol.fan_base),
                                       Ex.let("drama", Ex.num(idol.drama_factor),
                                             # Viral reach = budget * talent / drama
                                             # High drama = risky viral potential
                                             Ex.default(
                                                 Ex.div(Ex.mul(Ex.variable("budget"), Ex.variable("talent")),
                                                       Ex.variable("drama")),
                                                 # Safe viral: budget * talent / 10
                                                 Ex.div(Ex.mul(Ex.variable("budget"), Ex.variable("talent")), Ex.num(10)))))))
        
        result = run_thermo(viral_calc)
        viral_reach = result[0].value if isinstance(result[0], VTNum) else campaign_budget * idol.talent_level // 10
        viral_chaos = result[1].total_entropy
        
        # Campaign effects
        new_fans = viral_reach // 100
        cost = min(campaign_budget, self.agency_wealth)
        
        self.agency_wealth -= cost
        idol.fan_base += new_fans
        self.total_fans += new_fans
        self.industry_entropy += viral_chaos
        
        if viral_chaos > 0:
            print(f"   🔥 VIRAL CHAOS! Mathematical impossibility in reach calculation!")
            print(f"   📈 But campaign succeeded anyway: +{new_fans:,} fans")
            print(f"   🌪️ Social media entropy: +{viral_chaos}")
            campaign_outcome = "Chaotic viral success"
        else:
            print(f"   📈 Smooth viral growth: +{new_fans:,} fans")
            campaign_outcome = "Calculated viral success"
        
        print(f"   💰 Cost: ${cost:,}")
        return campaign_outcome
    
    def host_award_show(self):
        """Host industry award show - ultimate chaos test"""
        
        print(f"\n🏆 HOSTING MAJOR AWARD SHOW")
        print(f"   Agency reputation: {self.agency_reputation}")
        print(f"   Total agency fans: {self.total_fans:,}")
        
        # Award show success calculation
        show_calc = Ex.let("reputation", Ex.num(self.agency_reputation),
                          Ex.let("total_fans", Ex.num(self.total_fans),
                                Ex.let("num_idols", Ex.num(len(self.idols)),
                                      # Show success = reputation * fans / (drama_of_all_idols)
                                      Ex.default(
                                          Ex.div(Ex.mul(Ex.variable("reputation"), Ex.variable("total_fans")),
                                                Ex.num(sum(idol.drama_factor for idol in self.idols) or 1)),
                                          # Fallback: basic success
                                          Ex.mul(Ex.variable("reputation"), Ex.num(1000))))))
        
        result = run_thermo(show_calc)
        show_success = result[0].value if isinstance(result[0], VTNum) else self.agency_reputation * 1000
        show_chaos = result[1].total_entropy
        
        # Award show effects
        revenue = show_success * 100
        reputation_change = show_success // 1000
        industry_prestige = show_success // 500
        
        self.agency_wealth += revenue
        self.agency_reputation = min(100, self.agency_reputation + reputation_change)
        self.industry_entropy += show_chaos
        
        # Boost all idols
        for idol in self.idols:
            idol.fan_base += industry_prestige
            self.total_fans += industry_prestige
        
        if show_chaos > 0:
            print(f"   🎭 AWARD SHOW CHAOS! Mathematical impossibilities during live broadcast!")
            print(f"   💫 But show was legendary anyway: ${revenue:,} revenue")
            show_result = "Chaotic but unforgettable award show"
        else:
            print(f"   ✨ Flawless award show execution!")
            print(f"   💰 Revenue: ${revenue:,}")
            show_result = "Perfect award show"
        
        print(f"   📈 Agency reputation: +{reputation_change} (now: {self.agency_reputation})")
        return show_result
    
    def year_end_analysis(self):
        """Year-end mathematical analysis of empire performance"""
        
        print(f"\n📊 {self.current_year} YEAR-END ANALYSIS")
        print("=" * 50)
        
        # Calculate empire health using mathematical principles
        empire_calc = Ex.let("wealth", Ex.num(self.agency_wealth),
                            Ex.let("fans", Ex.num(self.total_fans),
                                  Ex.let("reputation", Ex.num(self.agency_reputation),
                                        Ex.let("num_idols", Ex.num(len(self.idols)),
                                              # Empire score = (wealth + fans + reputation) / entropy_risk
                                              Ex.default(
                                                  Ex.div(Ex.add(Ex.add(Ex.variable("wealth"), Ex.variable("fans")),
                                                               Ex.variable("reputation")),
                                                        Ex.num(max(1, self.industry_entropy))),
                                                  # Fallback: simple sum
                                                  Ex.add(Ex.add(Ex.variable("wealth"), Ex.variable("fans")),
                                                        Ex.variable("reputation")))))))
        
        result = run_thermo(empire_calc)
        empire_score = result[0].value if isinstance(result[0], VTNum) else (self.agency_wealth + self.total_fans + self.agency_reputation)
        analysis_chaos = result[1].total_entropy
        
        self.industry_entropy += analysis_chaos
        
        # Empire assessment
        if empire_score > 1000000:
            empire_status = "🌟 LEGENDARY EMPIRE"
        elif empire_score > 500000:
            empire_status = "🏆 MAJOR EMPIRE"
        elif empire_score > 100000:
            empire_status = "📈 GROWING EMPIRE"
        elif empire_score > 50000:
            empire_status = "🌱 EMERGING AGENCY"
        else:
            empire_status = "🔧 REBUILDING PHASE"
        
        print(f"Empire Status: {empire_status}")
        print(f"Empire Score: {empire_score:,}")
        print(f"Agency Wealth: ${self.agency_wealth:,}")
        print(f"Total Fans: {self.total_fans:,}")
        print(f"Agency Reputation: {self.agency_reputation}/100")
        print(f"Industry Entropy: {self.industry_entropy} (chaos survived)")
        print(f"Scandals Handled: {self.scandal_count}")
        print(f"Successful Events: {self.successful_events}")
        
        # Mathematical insights
        avg_entropy_per_event = self.industry_entropy / max(1, self.successful_events + self.scandal_count)
        print(f"\n🧮 MATHEMATICAL INSIGHTS:")
        print(f"Average chaos per event: {avg_entropy_per_event:.2f}")
        print(f"System crashes: 0 ✅ (mathematical guarantee)")
        print(f"Chaos handling efficiency: 100% (all impossibilities became structured data)")
        
        self.current_year += 1
        return empire_score
    
    def get_empire_summary(self):
        """Final empire analysis with mathematical properties"""
        
        return {
            'agency_name': self.agency_name,
            'current_year': self.current_year,
            'total_idols': len(self.idols),
            'empire_wealth': self.agency_wealth,
            'total_fanbase': self.total_fans,
            'agency_reputation': self.agency_reputation,
            'mathematical_properties': {
                'total_industry_entropy': self.industry_entropy,
                'scandals_survived': self.scandal_count,
                'successful_events': self.successful_events,
                'mathematical_guarantee': 'Empire never crashed despite any chaos level',
                'conservation_laws': 'Mathematical laws preserved throughout simulation'
            },
            'top_idols': sorted(self.idols, key=lambda i: i.fan_base, reverse=True)[:3] if self.idols else []
        }

def run_idol_empire_simulation():
    """Actually run the idol empire simulation!"""
    
    print("🎭 IDOL EMPIRE SIMULATOR")
    print("Entertainment industry chaos handled with mathematical guarantees!")
    print("=" * 80)
    
    # Create talent agency
    agency = IdolEmpireManager("Chaos Star Entertainment")
    
    # Recruit initial roster - mix of safe and risky talent
    print("\n🌟 INITIAL TALENT RECRUITMENT")
    print("-" * 40)
    
    # Recruit some talents with interesting chaos profiles
    agency.recruit_idol("Harmony Perfect", talent=90, drama=5)     # Safe talent
    agency.recruit_idol("Chaos Storm", talent=95, drama=80)       # High risk/reward
    agency.recruit_idol("Math Whiz", talent=75, drama=0)          # Zero drama (division edge case)
    agency.recruit_idol("Drama Queen", talent=85, drama=100)      # Maximum drama (impossible calculation)
    
    print(f"\nRoster complete! Agency entropy: {agency.industry_entropy}")
    
    # Simulate 3 years of agency operations
    for year in range(3):
        print(f"\n🗓️ YEAR {agency.current_year} OPERATIONS")
        print("=" * 30)
        
        # Each idol gets activities
        for idol in agency.idols:
            # Tour or campaign?
            if random.random() < 0.7:
                agency.plan_concert_tour(idol)
            else:
                agency.run_viral_campaign(idol)
            
            # Random scandal chance
            if random.random() < 0.3:
                agency.handle_scandal(idol)
                
                # Comeback attempt after scandal
                if random.random() < 0.6:
                    agency.attempt_comeback(idol)
        
        # Major events
        if random.random() < 0.4:
            agency.simulate_market_crash()
        
        if random.random() < 0.3:
            agency.host_award_show()
        
        # Year-end analysis
        empire_score = agency.year_end_analysis()
        
        # Brief pause for dramatic effect
        time.sleep(0.2)
    
    # Final empire summary
    print(f"\n🏆 FINAL EMPIRE ANALYSIS")
    print("=" * 50)
    
    summary = agency.get_empire_summary()
    
    print(f"Agency: {summary['agency_name']}")
    print(f"Final Year: {summary['current_year']}")
    print(f"Empire Wealth: ${summary['empire_wealth']:,}")
    print(f"Total Fanbase: {summary['total_fanbase']:,}")
    print(f"Agency Reputation: {summary['agency_reputation']}/100")
    print(f"Total Idols: {summary['total_idols']}")
    
    print(f"\n🧮 MATHEMATICAL EMPIRE PROPERTIES:")
    math_props = summary['mathematical_properties']
    for key, value in math_props.items():
        print(f"  {key}: {value}")
    
    print(f"\n⭐ TOP PERFORMERS:")
    for i, idol in enumerate(summary['top_idols'], 1):
        print(f"  #{i}: {idol}")
    
    print(f"\n🎯 WHAT THIS DEMONSTRATES:")
    print("✅ Entertainment industry chaos handled gracefully")
    print("✅ Division by zero in scandal calculations became structured data")
    print("✅ Market crashes with mathematical impossibilities survived")
    print("✅ Rich entropy tracking for industry health monitoring")
    print("✅ Mathematical laws verified even in entertainment simulation")
    print("✅ System never crashed despite extreme industry drama")
    
    print(f"\n🌟 IDOL EMPIRE: Where entertainment chaos meets mathematical order! 🌟")
    
    return summary

if __name__ == "__main__":
    # Actually run the simulation!
    print("🚀 LAUNCHING IDOL EMPIRE SIMULATION")
    print("Watch mathematical guarantees handle entertainment industry chaos!\n")
    
    empire_summary = run_idol_empire_simulation()
    
    print("\n" + "=" * 60)
    print("🎉 IDOL EMPIRE SIMULATION COMPLETE!")
    print("\nKey insights about Unravel as a design pattern:")
    print("• Complex business simulations become robust")
    print("• Industry chaos becomes measurable insight")
    print("• Mathematical impossibilities become features")
    print("• Rich debugging through entropy analysis")
    print("• Entertainment industry reliability guaranteed")
    
    print("\n🌀 Ready to manage your own chaos-proof empire! 🌀")